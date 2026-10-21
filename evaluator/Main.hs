{-# OPTIONS_GHC -Wall #-}
-- The TRIEL core evaluator: reads a core specification and an implementation
-- trace as one S-expression on standard input, runs the function "run"
-- exported from formal/core/TRIEL_Exec.thy (generated/TRIEL.hs), and prints
-- the report in the format of examples/core/README.md.
--
-- Only reading the input and printing the report are written here; every
-- verdict comes from the exported code. The input is produced by
-- parser/triel_eval.py. Its grammar:
--
--   input  ::= (input (spec (factors F*) (terms T*) (invariants I*)) (trace E*))
--   F      ::= (factor NAME TY AGE) | (hidden_factor NAME TY AGE)
--   AGE    ::= (none) | (block INT)
--   TY     ::= (prim bool|int|decimal|string|datetime) | (optional TY)
--            | (record (NAME TY)*)
--   T      ::= (must NAME ACT DL ST) | (must_not NAME ACT X) | (may NAME ACT X)
--            | (then T T) | (or T T) | (and T T) | (unless T X T)
--            | (if X T T) | (skip) | (ref INT) | (on_breach NAME A*)
--            | (must_else NAME ACT DL NAME ACT DL)  -- WITHIN ... ELSE, first DL not (none)
--   ACT    ::= NAME | (action NAME ARG*)    ARG ::= PATH | VAL
--   DL     ::= (none) | (at INT) | (after INT) | (factor PATH INT)
--   ST     ::= (none) | (at INT) | (factor PATH INT)       -- FROM
--   A      ::= (notify NAME) | (penalty P CAP) | (terminate) | (cure_by INT)
--            | (escalate_to NAME)
--   P      ::= (val V) | (add P P) | (sub P P) | (mul P P) | (neg P)
--   CAP    ::= (none) | VAL
--   X      ::= (true) | (false) | (eq V V) | (lt V V) | (le V V) | (not X)
--            | (and X X) | (or X X) | (implies X X) | (present PATH)
--   V      ::= (const VAL) | (name PATH) | (default PATH V)
--   PATH   ::= (path NAME*)
--   VAL    ::= (bool true|false) | (int INT) | (dec INT INT) | (str NAME) | (time INT)
--   I      ::= (invariant NAME (always X)|(eventually X)|(next X)
--                          |(eventually_within X DL))       -- DL not (none)
--   E      ::= (entry INT EV (data (NAME D)*))
--   EV     ::= (act NAME ACT must|may|must_not) | (arrive NAME) | (tick)
--   D      ::= VAL | (record (NAME D)*)
--
-- NAME is a string literal; INT is a decimal integer (seconds for times).
-- (dec M K) is the exact number M / 10^K; (int N) is the number N.
-- (ref K) refers to the element K of (terms T*), counted from 0.

module Main (main) where

import Data.Char (isDigit, isSpace)
import Data.List (intercalate)
import System.Exit (exitWith, ExitCode (ExitFailure))
import System.IO (hPutStrLn, stderr)
import qualified TRIEL as T

data SExp = Sym String | Str String | List [SExp]
  deriving Show

-- Reading S-expressions.

tokenize :: String -> Either String [SExp]
tokenize s = case parseMany s of
  Right (xs, rest) | all isSpace (dropComments rest) -> Right xs
  Right (_, rest) -> Left ("unexpected " ++ take 20 rest)
  Left e -> Left e

dropComments :: String -> String
dropComments (';' : r) = dropComments (dropWhile (/= '\n') r)
dropComments (c : r) | isSpace c = dropComments r
dropComments r = r

parseMany :: String -> Either String ([SExp], String)
parseMany s = case dropComments s of
  "" -> Right ([], "")
  r@(')' : _) -> Right ([], r)
  r -> do
    (x, r') <- parseOne r
    (xs, r'') <- parseMany r'
    return (x : xs, r'')

parseOne :: String -> Either String (SExp, String)
parseOne ('(' : r) = do
  (xs, r') <- parseMany r
  case r' of
    ')' : r'' -> Right (List xs, r'')
    _ -> Left "missing )"
parseOne ('"' : r) = str "" r
  where
    str acc ('\\' : c : t) = str (unesc c : acc) t
    str acc ('"' : t) = Right (Str (reverse acc), t)
    str acc (c : t) = str (c : acc) t
    str _ [] = Left "unterminated string"
    unesc 'n' = '\n'
    unesc 't' = '\t'
    unesc c = c
parseOne r =
  let (a, t) = break (\c -> isSpace c || c `elem` "()\";") r
  in if null a then Left ("unexpected " ++ take 20 r) else Right (Sym a, t)

-- Converting to the exported datatypes.

type Conv a = SExp -> Either String a

bad :: String -> SExp -> Either String a
bad what x = Left ("expected " ++ what ++ ", got " ++ take 80 (show x))

name :: Conv String
name (Str s) = Right s
name x = bad "a name" x

integer :: Conv Integer
integer (Sym ('-' : ds)) | not (null ds), all isDigit ds = Right (negate (read ds))
integer (Sym ds) | not (null ds), all isDigit ds = Right (read ds)
integer x = bad "an integer" x

int :: Conv T.Int
int x = T.Int_of_integer <$> integer x

path :: Conv [String]
path (List (Sym "path" : ns)) = mapM name ns
path x = bad "a path" x

value :: Conv T.Atom
value (List [Sym "bool", Sym "true"]) = Right (T.ABool True)
value (List [Sym "bool", Sym "false"]) = Right (T.ABool False)
value (List [Sym "int", n]) = T.dec_atom <$> int n <*> pure (T.nat_of_integer 0)
value (List [Sym "dec", m, k]) = do
  k' <- integer k
  if k' < 0 then bad "a number of decimal places" k
  else T.dec_atom <$> int m <*> pure (T.nat_of_integer k')
value (List [Sym "str", s]) = T.AStr <$> name s
value (List [Sym "time", n]) = T.ATime <$> int n
value x = bad "a value" x

ty :: Conv (T.Ty String T.Prim)
ty (List [Sym "prim", Sym p]) = case p of
  "bool" -> Right (T.TPrim T.PBool)
  "int" -> Right (T.TPrim T.PInt)
  "decimal" -> Right (T.TPrim T.PDec)
  "string" -> Right (T.TPrim T.PStr)
  "datetime" -> Right (T.TPrim T.PTime)
  _ -> bad "a primitive type" (Sym p)
ty (List [Sym "optional", t]) = T.TOptional <$> ty t
ty (List (Sym "record" : fs)) = T.TRecord <$> mapM field fs
  where
    field (List [f, t]) = (,) <$> name f <*> ty t
    field x = bad "a field" x
ty x = bad "a type" x

vexp :: Conv (T.Vexp [String] T.Atom)
vexp (List [Sym "const", v]) = T.VConst <$> value v
vexp (List [Sym "name", p]) = T.VName <$> path p
vexp (List [Sym "default", p, v]) = T.VDefault <$> path p <*> vexp v
vexp x = bad "a value expression" x

expr :: Conv (T.Expr [String] T.Atom)
expr (List [Sym "true"]) = Right T.ETrue
expr (List [Sym "false"]) = Right T.EFalse
expr (List [Sym "eq", a, b]) = T.EEq <$> vexp a <*> vexp b
expr (List [Sym "lt", a, b]) = T.ELt <$> vexp a <*> vexp b
expr (List [Sym "le", a, b]) = T.ELe <$> vexp a <*> vexp b
expr (List [Sym "not", e]) = T.ENot <$> expr e
expr (List [Sym "and", a, b]) = T.EAnd <$> expr a <*> expr b
expr (List [Sym "or", a, b]) = T.EOr <$> expr a <*> expr b
expr (List [Sym "implies", a, b]) = T.EImp <$> expr a <*> expr b
expr (List [Sym "present", p]) = T.EPresent <$> path p
expr x = bad "an expression" x

deadline :: Conv (Maybe (T.Deadline [String]))
deadline (List [Sym "none"]) = Right Nothing
deadline (List [Sym "at", n]) = Just . T.DAt <$> int n
deadline (List [Sym "after", n]) = Just . T.DAfter <$> int n
deadline (List [Sym "factor", p, n]) = Just <$> (T.DFactor <$> path p <*> int n)
deadline x = bad "a deadline" x

start :: Conv (Maybe (T.Deadline [String]))
start (List [Sym "none"]) = Right Nothing
start (List [Sym "at", n]) = Just . T.DAt <$> int n
start (List [Sym "factor", p, n]) = Just <$> (T.DFactor <$> path p <*> int n)
start x = bad "a start (FROM)" x

-- An action: a name, or a name with arguments; an argument is a path or a value.
act :: Conv T.Act
act (Str a) = Right (T.Act a [])
act (List (Sym "action" : a : xs)) = T.Act <$> name a <*> mapM arg xs
  where
    arg x@(List (Sym "path" : _)) = T.ArgName <$> path x
    arg x = T.ArgVal <$> value x
act x = bad "an action" x

pexp :: Conv (T.Pexp [String] T.Atom)
pexp (List [Sym "val", v]) = T.PVal <$> vexp v
pexp (List [Sym "add", a, b]) = T.PAdd <$> pexp a <*> pexp b
pexp (List [Sym "sub", a, b]) = T.PSub <$> pexp a <*> pexp b
pexp (List [Sym "mul", a, b]) = T.PMul <$> pexp a <*> pexp b
pexp (List [Sym "neg", a]) = T.PNeg <$> pexp a
pexp x = bad "an amount" x

cap :: Conv (Maybe T.Rat)
cap (List [Sym "none"]) = Right Nothing
cap x = value x >>= \v -> maybe (bad "a numeric cap" x) (Right . Just) (T.num_of v)

action :: Conv (T.Baction String (T.Pen [String] T.Atom))
action (List [Sym "notify", s]) = T.Notify <$> name s
action (List [Sym "penalty", e, c]) = T.Penalty <$> (T.Pen <$> pexp e <*> cap c)
action (List [Sym "terminate"]) = Right T.Terminate
action (List [Sym "cure_by", n]) = T.CureBy <$> int n
action (List [Sym "escalate_to", s]) = T.EscalateTo <$> name s
action x = bad "a breach action" x

term :: Conv (T.Sterm [String] T.Atom String T.Act (T.Pen [String] T.Atom))
term (List [Sym "must", s, a, d, f]) = T.SMust <$> name s <*> act a <*> deadline d <*> start f
term (List [Sym "must_not", s, a, c]) = T.SMustNot <$> name s <*> act a <*> expr c
term (List [Sym "may", s, a, c]) = T.SMay <$> name s <*> act a <*> expr c
term (List [Sym "then", t, u]) = T.SThen <$> term t <*> term u
term (List [Sym "or", t, u]) = T.SOr <$> term t <*> term u
term (List [Sym "and", t, u]) = T.SAnd <$> term t <*> term u
term (List [Sym "unless", t, c, u]) = T.SUnless <$> term t <*> expr c <*> term u
term (List [Sym "if", c, t, u]) = T.SIf <$> expr c <*> term t <*> term u
term (List [Sym "skip"]) = Right T.SSkip
term (List [Sym "ref", k]) = integer k >>= \n ->
  if n >= 0 then Right (T.SRef (T.nat_of_integer n)) else bad "an element index" k
term (List (Sym "on_breach" : s : as)) = T.SOnBreach <$> name s <*> mapM action as
term (List [Sym "must_else", s, a, d, s', a', d']) = do
  dl <- deadline d
  case dl of
    Just e -> T.SMustElse <$> name s <*> act a <*> pure e <*> name s' <*> act a' <*> deadline d'
    Nothing -> bad "a deadline" d
term x = bad "a term" x

-- A hidden factor (a ZK<T> factor without WITHOUT REVEALING ALL) is removed from
-- the data of every entry before evaluation.
factor :: Conv T.Fdecl
factor (List [Sym k, f, t, a])
  | k == "factor" || k == "hidden_factor" =
      T.Fdecl <$> name f <*> ty t <*> age a <*> pure (k == "hidden_factor")
  where
    age (List [Sym "none"]) = Right Nothing
    age (List [Sym "block", n]) = Just <$> int n
    age x = bad "(none) or (block N)" x
factor x = bad "a factor" x

invariant :: Conv (String, T.Sinv [String] T.Atom)
invariant (List [Sym "invariant", n, List [Sym "eventually_within", e, d]]) = do
  n' <- name n
  e' <- expr e
  d' <- deadline d
  case d' of
    Just dl -> Right (n', T.SEventuallyWithin e' dl)
    Nothing -> bad "a deadline" d
invariant (List [Sym "invariant", n, List [Sym op, e]]) = do
  n' <- name n
  e' <- expr e
  case op of
    "always" -> Right (n', T.SInv (T.Always e'))
    "eventually" -> Right (n', T.SInv (T.Eventually e'))
    "next" -> Right (n', T.SInv (T.Next e'))
    _ -> bad "always, eventually, next or eventually_within" (Sym op)
invariant x = bad "an invariant" x

datum :: Conv (T.Nd String T.Atom)
datum (List (Sym "record" : fs)) = T.Nom . T.Fmap_of_list <$> mapM field fs
  where
    field (List [f, d]) = (,) <$> name f <*> datum d
    field x = bad "a field" x
datum x = T.Atom <$> value x

event :: Conv (T.Event [String] String T.Act)
event (List [Sym "act", s, a, Sym p]) = do
  pol <- case p of
    "must" -> Right T.Must
    "may" -> Right T.May
    "must_not" -> Right T.MustNot
    _ -> bad "must, may or must_not" (Sym p)
  T.Deontic <$> name s <*> act a <*> pure pol
event (List [Sym "arrive", f]) = (\n -> T.Arrival [n]) <$> name f
event (List [Sym "tick"]) = Right T.Tick
event x = bad "an event" x

entry :: Conv (T.Nd String T.Atom, (T.Int, T.Event [String] String T.Act))
entry (List [Sym "entry", t, e, List (Sym "data" : ds)]) = do
  t' <- int t
  e' <- event e
  d <- datum (List (Sym "record" : ds))
  return (d, (t', e'))
entry x = bad "an entry" x

input :: Conv (T.Spec, [(T.Nd String T.Atom, (T.Int, T.Event [String] String T.Act))])
input (List [Sym "input",
             List [Sym "spec", List (Sym "factors" : fs), List (Sym "terms" : ts),
                   List (Sym "invariants" : is)],
             List (Sym "trace" : es)]) = do
  sp <- T.Spec <$> mapM factor fs <*> mapM term ts <*> mapM invariant is
  tr <- mapM entry es
  return (sp, tr)
input x = bad "(input (spec ...) (trace ...))" x

-- Printing the report.

nat :: T.Nat -> String
nat = show . T.integer_of_nat

tm :: T.Int -> String
tm = show . T.integer_of_int

verdict :: T.Verdict -> String
verdict T.Fulfilled = "FULFILLED"
verdict T.Pending = "PENDING"
verdict (T.Breached t) = "BREACHED " ++ tm t

-- The informational actions of the handler follow BREACHED T: they fire at the breach.
status :: T.Status String -> [T.Ract String] -> String
status T.SFulfilled _ = "FULFILLED"
status T.SPending _ = "PENDING"
status (T.SBreached t c) acts =
  "BREACHED " ++ tm t ++ concatMap ((' ' :) . ract) acts ++ " " ++ continuation c
  where
    continuation T.NoContinuation = "CLOSED"
    continuation T.Terminated = "TERMINATED"
    continuation (T.Cure v) = "CURE " ++ verdict v
    continuation (T.Escalated s v) = "ESCALATED " ++ s ++ " " ++ verdict v

-- A number in lowest terms a/b is printed exactly: with the fewest decimal places
-- when b divides a power of 10 (every number written as a literal), and as a
-- fraction otherwise.
number :: T.Rat -> String
number q =
  let (a, b) = T.quotient_of q
      n = T.integer_of_int a
      d = T.integer_of_int b
      places = [k | k <- [0 .. 4 * length (show d)], (10 ^ k) `mod` d == 0]
  in case places of
       k : _ ->
         let m = abs n * (10 ^ k `div` d)
             ds = show m
             padded = replicate (k + 1 - length ds) '0' ++ ds
             (whole, frac) = splitAt (length padded - k) padded
         in (if n < 0 then "-" else "") ++ whole ++ (if k == 0 then "" else '.' : frac)
       [] -> show n ++ "/" ++ show d

atom :: T.Atom -> String
atom (T.ABool b) = if b then "true" else "false"
atom (T.ANum q) = number q
atom (T.AStr s) = show s
atom (T.ATime t) = tm t

-- A breached norm is reported with the informational actions of its handler,
-- the penalties with their amounts in the state of the breach.
ract :: T.Ract String -> String
ract (T.RNotify s) = "NOTIFY " ++ s
ract (T.RPenalty (T.PAmount q capped)) = "PENALTY " ++ number q ++ (if capped then " CAPPED" else "")
ract (T.RPenalty T.PUndefined) = "PENALTY UNDEFINED"
ract (T.RPenalty (T.PNegative q)) = "PENALTY NEGATIVE " ++ number q

showAct :: T.Act -> String
showAct (T.Act a []) = a
showAct (T.Act a xs) = a ++ "(" ++ intercalate ", " (map arg xs) ++ ")"
  where
    arg (T.ArgName p) = intercalate "." p
    arg (T.ArgVal v) = atom v

answer :: Maybe Bool -> String
answer (Just True) = "YES"
answer (Just False) = "NO"
answer Nothing = "UNKNOWN"

truth :: Maybe Bool -> String
truth (Just True) = "T"
truth (Just False) = "F"
truth Nothing = "U"

line :: T.Line -> String
line (T.LTimeOrder j) = "TIME ORDER REJECTED ENTRY " ++ nat j
line (T.LActivation b) = "ACTIVATION " ++ (if b then "OK" else "REJECTED")
line (T.LBlock b) = "BLOCK " ++ (if b then "OK" else "REJECTED")
line (T.LTypes Nothing) = "TYPES OK"
line (T.LTypes (Just (j, f))) = "TYPES ILL-TYPED ENTRY " ++ nat j ++ " FACTOR " ++ f
line (T.LMust i s a d st acts) =
  "TERM " ++ nat i ++ " MUST " ++ s ++ " " ++ showAct a ++ " DEADLINE "
    ++ maybe "NONE" tm d ++ " : " ++ status st acts
line (T.LMustNot i s a v acts) =
  "TERM " ++ nat i ++ " MUST_NOT " ++ s ++ " " ++ showAct a ++ " : " ++ verdict v
    ++ concatMap ((' ' :) . ract) acts
line (T.LMustElse i s a d s' a' d' st) =
  "TERM " ++ nat i ++ " MUST " ++ s ++ " " ++ showAct a ++ " DEADLINE " ++ maybe "NONE" tm d
    ++ " ELSE " ++ s' ++ " " ++ showAct a' ++ " DEADLINE " ++ maybe "NONE" tm d' ++ " : " ++ elseStatus st
  where
    elseStatus T.EFulfilled = "FULFILLED"
    elseStatus T.EPending = "PENDING"
    elseStatus (T.EElse _ v) = "ELSE " ++ verdict v
line (T.LMay i s a v) = "TERM " ++ nat i ++ " MAY " ++ s ++ " " ++ showAct a ++ " : " ++ verdict v
line (T.LOnBreach i s j) =
  "TERM " ++ nat i ++ " ON_BREACH " ++ s ++ " : " ++ maybe "UNBOUND" (("BOUND " ++) . nat) j
line (T.LComposite i d n v p) =
  "TERM " ++ nat i ++ " COMPOSITE : DONE " ++ answer d ++ " INTERRUPTED " ++ answer n
    ++ " VIOLATED " ++ answer v ++ " STATUS " ++ termStatus p
  where
    termStatus (T.CAt o k) = outcome o ++ " ENTRY " ++ nat k
    termStatus T.COpen = "OPEN"
    termStatus T.CUnknown = "UNKNOWN"
    outcome T.Violated = "VIOLATED"
    outcome T.Interrupted = "INTERRUPTED"
    outcome T.Done = "DONE"
line (T.LInvariant n b) = "INVARIANT " ++ n ++ " : " ++ truth b

main :: IO ()
main = do
  src <- getContents
  case tokenize src >>= one >>= input of
    Left e -> do
      hPutStrLn stderr ("evaluator: " ++ e)
      exitWith (ExitFailure 1)
    Right (sp, tr) -> mapM_ (putStrLn . line) (T.run sp tr)
  where
    one [x] = Right x
    one xs = Left ("expected one S-expression, got " ++ show (length xs))
