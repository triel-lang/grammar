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
--   F      ::= (factor NAME TY AGE)          AGE ::= (none) | (block INT)
--   TY     ::= (prim bool|int|string|datetime) | (optional TY) | (record (NAME TY)*)
--   T      ::= (must NAME NAME DL) | (must_not NAME NAME X) | (may NAME NAME X)
--            | (then T T) | (or T T) | (and T T) | (unless T X T)
--            | (on_breach NAME A*)
--   DL     ::= (none) | (at INT) | (after INT) | (factor PATH INT)
--   A      ::= (notify NAME) | (penalty VAL) | (terminate) | (cure_by INT)
--            | (escalate_to NAME)
--   X      ::= (true) | (false) | (eq V V) | (not X) | (and X X) | (or X X)
--            | (implies X X) | (present PATH)
--   V      ::= (const VAL) | (name PATH)       PATH ::= (path NAME*)
--   VAL    ::= (bool true|false) | (int INT) | (str NAME) | (time INT)
--   I      ::= (invariant NAME (always X)|(eventually X)|(next X))
--   E      ::= (entry INT EV (data (NAME D)*))
--   EV     ::= (act NAME NAME must|may|must_not) | (arrive NAME) | (tick)
--   D      ::= VAL | (record (NAME D)*)
--
-- NAME is a string literal; INT is a decimal integer (seconds for times).

module Main (main) where

import Data.Char (isDigit, isSpace)
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
value (List [Sym "int", n]) = T.AInt <$> int n
value (List [Sym "str", s]) = T.AStr <$> name s
value (List [Sym "time", n]) = T.ATime <$> int n
value x = bad "a value" x

ty :: Conv (T.Ty String T.Prim)
ty (List [Sym "prim", Sym p]) = case p of
  "bool" -> Right (T.TPrim T.PBool)
  "int" -> Right (T.TPrim T.PInt)
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
vexp x = bad "a value expression" x

expr :: Conv (T.Expr [String] T.Atom)
expr (List [Sym "true"]) = Right T.ETrue
expr (List [Sym "false"]) = Right T.EFalse
expr (List [Sym "eq", a, b]) = T.EEq <$> vexp a <*> vexp b
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

action :: Conv (T.Baction String T.Atom)
action (List [Sym "notify", s]) = T.Notify <$> name s
action (List [Sym "penalty", v]) = T.Penalty <$> value v
action (List [Sym "terminate"]) = Right T.Terminate
action (List [Sym "cure_by", n]) = T.CureBy <$> int n
action (List [Sym "escalate_to", s]) = T.EscalateTo <$> name s
action x = bad "a breach action" x

term :: Conv (T.Sterm [String] T.Atom String String T.Atom)
term (List [Sym "must", s, a, d]) = T.SMust <$> name s <*> name a <*> deadline d
term (List [Sym "must_not", s, a, c]) = T.SMustNot <$> name s <*> name a <*> expr c
term (List [Sym "may", s, a, c]) = T.SMay <$> name s <*> name a <*> expr c
term (List [Sym "then", t, u]) = T.SThen <$> term t <*> term u
term (List [Sym "or", t, u]) = T.SOr <$> term t <*> term u
term (List [Sym "and", t, u]) = T.SAnd <$> term t <*> term u
term (List [Sym "unless", t, c, u]) = T.SUnless <$> term t <*> expr c <*> term u
term (List (Sym "on_breach" : s : as)) = T.SOnBreach <$> name s <*> mapM action as
term x = bad "a term" x

factor :: Conv T.Fdecl
factor (List [Sym "factor", f, t, a]) = T.Fdecl <$> name f <*> ty t <*> age a
  where
    age (List [Sym "none"]) = Right Nothing
    age (List [Sym "block", n]) = Just <$> int n
    age x = bad "(none) or (block N)" x
factor x = bad "a factor" x

invariant :: Conv (String, T.Inv [String] T.Atom)
invariant (List [Sym "invariant", n, List [Sym op, e]]) = do
  n' <- name n
  e' <- expr e
  case op of
    "always" -> Right (n', T.Always e')
    "eventually" -> Right (n', T.Eventually e')
    "next" -> Right (n', T.Next e')
    _ -> bad "always, eventually or next" (Sym op)
invariant x = bad "an invariant" x

datum :: Conv (T.Nd String T.Atom)
datum (List (Sym "record" : fs)) = T.Nom . T.Fmap_of_list <$> mapM field fs
  where
    field (List [f, d]) = (,) <$> name f <*> datum d
    field x = bad "a field" x
datum x = T.Atom <$> value x

event :: Conv (T.Event [String] String String)
event (List [Sym "act", s, a, Sym p]) = do
  pol <- case p of
    "must" -> Right T.Must
    "may" -> Right T.May
    "must_not" -> Right T.MustNot
    _ -> bad "must, may or must_not" (Sym p)
  T.Deontic <$> name s <*> name a <*> pure pol
event (List [Sym "arrive", f]) = (\n -> T.Arrival [n]) <$> name f
event (List [Sym "tick"]) = Right T.Tick
event x = bad "an event" x

entry :: Conv (T.Nd String T.Atom, (T.Int, T.Event [String] String String))
entry (List [Sym "entry", t, e, List (Sym "data" : ds)]) = do
  t' <- int t
  e' <- event e
  d <- datum (List (Sym "record" : ds))
  return (d, (t', e'))
entry x = bad "an entry" x

input :: Conv (T.Spec, [(T.Nd String T.Atom, (T.Int, T.Event [String] String String))])
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

status :: T.Status String -> String
status T.SFulfilled = "FULFILLED"
status T.SPending = "PENDING"
status (T.SBreached t c) = "BREACHED " ++ tm t ++ " " ++ continuation c
  where
    continuation T.NoContinuation = "CLOSED"
    continuation T.Terminated = "TERMINATED"
    continuation (T.Cure v) = "CURE " ++ verdict v
    continuation (T.Escalated s v) = "ESCALATED " ++ s ++ " " ++ verdict v

answer :: Maybe Bool -> String
answer (Just True) = "YES"
answer (Just False) = "NO"
answer Nothing = "UNKNOWN"

truth :: Maybe Bool -> String
truth (Just True) = "T"
truth (Just False) = "F"
truth Nothing = "U"

line :: T.Line -> String
line (T.LActivation b) = "ACTIVATION " ++ (if b then "OK" else "REJECTED")
line (T.LBlock b) = "BLOCK " ++ (if b then "OK" else "REJECTED")
line (T.LTypes Nothing) = "TYPES OK"
line (T.LTypes (Just (j, f))) = "TYPES ILL-TYPED ENTRY " ++ nat j ++ " FACTOR " ++ f
line (T.LMust i s a d st) =
  "TERM " ++ nat i ++ " MUST " ++ s ++ " " ++ a ++ " DEADLINE "
    ++ maybe "NONE" tm d ++ " : " ++ status st
line (T.LMustNot i s a v) = "TERM " ++ nat i ++ " MUST_NOT " ++ s ++ " " ++ a ++ " : " ++ verdict v
line (T.LMay i s a v) = "TERM " ++ nat i ++ " MAY " ++ s ++ " " ++ a ++ " : " ++ verdict v
line (T.LOnBreach i s j) =
  "TERM " ++ nat i ++ " ON_BREACH " ++ s ++ " : " ++ maybe "UNBOUND" (("BOUND " ++) . nat) j
line (T.LComposite i d n v) =
  "TERM " ++ nat i ++ " COMPOSITE : DONE " ++ answer d ++ " INTERRUPTED " ++ answer n
    ++ " VIOLATED " ++ answer v
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
