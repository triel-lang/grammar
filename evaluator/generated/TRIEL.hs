{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  TRIEL(Int(..), integer_of_int, Nat, integer_of_nat, Atom(..), Fmap(..),
         Nd(..), Ty(..), Vexp(..), Expr(..), Verdict(..), Baction(..),
         Continuation(..), Status(..), Line(..), Prim(..), Inv(..),
         Deadline(..), Sterm(..), Fdecl(..), Spec(..), Polarity(..), Event(..),
         nat_of_integer, run)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import Data.Bits ((.&.), (.|.), (.^.));
import qualified Prelude;
import qualified Data.Bits;

newtype Int = Int_of_integer Integer;

integer_of_int :: Int -> Integer;
integer_of_int (Int_of_integer k) = k;

less_eq_int :: Int -> Int -> Bool;
less_eq_int k l = integer_of_int k <= integer_of_int l;

class Ord a where {
  less_eq :: a -> a -> Bool;
  less :: a -> a -> Bool;
};

less_int :: Int -> Int -> Bool;
less_int k l = integer_of_int k < integer_of_int l;

instance Ord Int where {
  less_eq = less_eq_int;
  less = less_int;
};

class (Ord a) => Preorder a where {
};

class (Preorder a) => Order a where {
};

instance Preorder Int where {
};

instance Order Int where {
};

class (Order a) => Linorder a where {
};

instance Linorder Int where {
};

newtype Nat = Nat Integer;

integer_of_nat :: Nat -> Integer;
integer_of_nat (Nat x) = x;

equal_nat :: Nat -> Nat -> Bool;
equal_nat m n = integer_of_nat m == integer_of_nat n;

instance Eq Nat where {
  a == b = equal_nat a b;
};

equal_int :: Int -> Int -> Bool;
equal_int k l = integer_of_int k == integer_of_int l;

data Atom = ABool Bool | AInt Int | AStr String | ATime Int;

equal_atom :: Atom -> Atom -> Bool;
equal_atom (AStr x3) (ATime x4) = False;
equal_atom (ATime x4) (AStr x3) = False;
equal_atom (AInt x2) (ATime x4) = False;
equal_atom (ATime x4) (AInt x2) = False;
equal_atom (AInt x2) (AStr x3) = False;
equal_atom (AStr x3) (AInt x2) = False;
equal_atom (ABool x1) (ATime x4) = False;
equal_atom (ATime x4) (ABool x1) = False;
equal_atom (ABool x1) (AStr x3) = False;
equal_atom (AStr x3) (ABool x1) = False;
equal_atom (ABool x1) (AInt x2) = False;
equal_atom (AInt x2) (ABool x1) = False;
equal_atom (ATime x4) (ATime y4) = equal_int x4 y4;
equal_atom (AStr x3) (AStr y3) = x3 == y3;
equal_atom (AInt x2) (AInt y2) = equal_int x2 y2;
equal_atom (ABool x1) (ABool y1) = x1 == y1;

instance Eq Atom where {
  a == b = equal_atom a b;
};

instance Ord Integer where {
  less_eq = (\ a b -> a <= b);
  less = (\ a b -> a < b);
};

data Num = One | Bit0 Num | Bit1 Num;

newtype Fmap a b = Fmap_of_list [(a, b)];

data Nd a b = Atom b | Nom (Fmap a (Nd a b));

data Ty a b = TPrim b | TOptional (Ty a b) | TRecord [(a, Ty a b)];

data Vexp a b = VConst b | VName a;

data Expr a b = ETrue | EFalse | EEq (Vexp a b) (Vexp a b) | ENot (Expr a b)
  | EAnd (Expr a b) (Expr a b) | EOr (Expr a b) (Expr a b)
  | EImp (Expr a b) (Expr a b) | EPresent a;

data Tm a b c d = TMust c d | TMay c d (Expr a b) | TMustNot c d (Expr a b)
  | TThen (Tm a b c d) (Tm a b c d) | TOr (Tm a b c d) (Tm a b c d)
  | TUnless (Tm a b c d) (Expr a b) (Tm a b c d)
  | TAnd (Tm a b c d) (Tm a b c d);

data Verdict = Fulfilled | Breached Int | Pending;

data Baction a b = Notify a | Penalty b | Terminate | CureBy Int | EscalateTo a;

data Continuation a = NoContinuation | Terminated | Cure Verdict
  | Escalated a Verdict;

data Status a = SFulfilled | SPending | SBreached Int (Continuation a);

data Line = LActivation Bool | LBlock Bool | LTypes (Maybe (Nat, String))
  | LMust Nat String String (Maybe Int) (Status String)
  | LMustNot Nat String String Verdict [Baction String Atom]
  | LMay Nat String String Verdict | LOnBreach Nat String (Maybe Nat)
  | LComposite Nat (Maybe Bool) (Maybe Bool) (Maybe Bool)
  | LInvariant String (Maybe Bool);

data Prim = PBool | PInt | PStr | PTime;

data Inv a b = Always (Expr a b) | Eventually (Expr a b) | Next (Expr a b);

data Deadline a = DAt Int | DAfter Int | DFactor a Int;

data Sterm a b c d e = SMust c d (Maybe (Deadline a)) | SMustNot c d (Expr a b)
  | SMay c d (Expr a b) | SThen (Sterm a b c d e) (Sterm a b c d e)
  | SOr (Sterm a b c d e) (Sterm a b c d e)
  | SAnd (Sterm a b c d e) (Sterm a b c d e)
  | SUnless (Sterm a b c d e) (Expr a b) (Sterm a b c d e)
  | SOnBreach c [Baction c e];

data Fdecl = Fdecl String (Ty String Prim) (Maybe Int);

data Spec =
  Spec [Fdecl] [Sterm [String] Atom String String Atom]
    [(String, Inv [String] Atom)];

data Polarity = Must | May | MustNot;

data Event a b c = Deontic b c Polarity | Arrival a | Tick;

data Outcome = Done | Interrupted | Violated;

plus_nat :: Nat -> Nat -> Nat;
plus_nat m n = Nat (integer_of_nat m + integer_of_nat n);

one_nat :: Nat;
one_nat = Nat (1 :: Integer);

suc :: Nat -> Nat;
suc n = plus_nat n one_nat;

max :: forall a. (Ord a) => a -> a -> a;
max a b = (if less_eq a b then b else a);

minus_nat :: Nat -> Nat -> Nat;
minus_nat m n = Nat (max (0 :: Integer) (integer_of_nat m - integer_of_nat n));

zero_nat :: Nat;
zero_nat = Nat (0 :: Integer);

nth :: forall a. [a] -> Nat -> a;
nth (x : xs) n =
  (if equal_nat n zero_nat then x else nth xs (minus_nat n one_nat));

less_nat :: Nat -> Nat -> Bool;
less_nat m n = integer_of_nat m < integer_of_nat n;

upt :: Nat -> Nat -> [Nat];
upt i j = (if less_nat i j then i : upt (suc i) j else []);

drop :: forall a. Nat -> [a] -> [a];
drop n [] = [];
drop n (x : xs) =
  (if equal_nat n zero_nat then x : xs else drop (minus_nat n one_nat) xs);

find :: forall a. (a -> Bool) -> [a] -> Maybe a;
find uu [] = Nothing;
find p (x : xs) = (if p x then Just x else find p xs);

last :: forall a. [a] -> a;
last (x : xs) = (if null xs then x else last xs);

take :: forall a. Nat -> [a] -> [a];
take n [] = [];
take n (x : xs) =
  (if equal_nat n zero_nat then [] else x : take (minus_nat n one_nat) xs);

foldr :: forall a b. (a -> b -> b) -> [a] -> b -> b;
foldr f [] = id;
foldr f (x : xs) = f x . foldr f xs;

map_of :: forall a b. (Eq a) => [(a, b)] -> a -> Maybe b;
map_of [] k = Nothing;
map_of ((l, v) : ps) k = (if l == k then Just v else map_of ps k);

member :: forall a. (Eq a) => [a] -> a -> Bool;
member [] y = False;
member (x : xs) y = x == y || member xs y;

bind :: forall a b. Maybe a -> (a -> Maybe b) -> Maybe b;
bind Nothing f = Nothing;
bind (Just x) f = f x;

distinct :: forall a. (Eq a) => [a] -> Bool;
distinct [] = True;
distinct (x : xs) = not (member xs x) && distinct xs;

fmlookup :: forall a b. (Eq a) => Fmap a b -> a -> Maybe b;
fmlookup (Fmap_of_list m) = map_of m;

denaming :: forall a b. (Eq a) => a -> Nd a b -> Maybe (Nd a b);
denaming v (Nom m) = fmlookup m v;
denaming v (Atom b) = Nothing;

den_path :: forall a b. (Eq a) => [a] -> Nd a b -> Maybe (Nd a b);
den_path [] d = Just d;
den_path (x : p) d = (case denaming x d of {
                       Nothing -> Nothing;
                       Just a -> den_path p a;
                     });

flat :: forall a b. (Eq a) => Nd a b -> [a] -> Maybe b;
flat d p = (case den_path p d of {
             Nothing -> Nothing;
             Just (Atom a) -> Just a;
             Just (Nom _) -> Nothing;
           });

is_none :: forall a. Maybe a -> Bool;
is_none Nothing = True;
is_none (Just x) = False;

kor :: Maybe Bool -> Maybe Bool -> Maybe Bool;
kor p q =
  (if p == Just True || q == Just True then Just True
    else (if p == Just False && q == Just False then Just False else Nothing));

length_tailrec :: forall a. [a] -> Nat -> Nat;
length_tailrec [] n = n;
length_tailrec (x : xs) n = length_tailrec xs (suc n);

size_list :: forall a. [a] -> Nat;
size_list xs = length_tailrec xs zero_nat;

binds :: forall a b c d e. (Eq a) => a -> Sterm b c a d e -> Bool;
binds sa (SMust s a d) = s == sa;
binds sa (SMustNot s a c) = s == sa;
binds s (SMay v va vb) = False;
binds s (SThen v va) = False;
binds s (SOr v va) = False;
binds s (SAnd v va) = False;
binds s (SUnless v va vb) = False;
binds s (SOnBreach v va) = False;

bound_to ::
  forall a b c d e. (Eq c) => [Sterm a b c d e] -> Nat -> c -> Maybe Nat;
bound_to blk i s = let {
                     js = filter (\ j -> binds s (nth blk j)) (upt zero_nat i);
                   } in (if null js then Nothing else Just (last js));

handler_of ::
  forall a b c d e. (Eq c) => [Sterm a b c d e] -> Nat -> [Baction c e];
handler_of blk i =
  (case find (\ k -> (case nth blk k of {
                       SMust _ _ _ -> False;
                       SMustNot _ _ _ -> False;
                       SMay _ _ _ -> False;
                       SThen _ _ -> False;
                       SOr _ _ -> False;
                       SAnd _ _ -> False;
                       SUnless _ _ _ -> False;
                       SOnBreach s _ -> bound_to blk k s == Just i;
                     }))
          (upt zero_nat (size_list blk))
    of {
    Nothing -> [];
    Just k -> (case nth blk k of {
                SMust _ _ _ -> [];
                SMustNot _ _ _ -> [];
                SMay _ _ _ -> [];
                SThen _ _ -> [];
                SOr _ _ -> [];
                SAnd _ _ -> [];
                SUnless _ _ _ -> [];
                SOnBreach _ acts -> acts;
              });
  });

is_cont :: forall a b. Baction a b -> Bool;
is_cont Terminate = True;
is_cont (CureBy k) = True;
is_cont (EscalateTo s) = True;
is_cont (Notify s) = False;
is_cont (Penalty p) = False;

cont_free_prohibitions :: forall a b c d e. (Eq c) => [Sterm a b c d e] -> Bool;
cont_free_prohibitions blk =
  all (\ k ->
        (case nth blk k of {
          SMust _ _ _ -> True;
          SMustNot _ _ _ -> all (\ x -> not (is_cont x)) (handler_of blk k);
          SMay _ _ _ -> True;
          SThen _ _ -> True;
          SOr _ _ -> True;
          SAnd _ _ -> True;
          SUnless _ _ _ -> True;
          SOnBreach _ _ -> True;
        }))
    (upt zero_nat (size_list blk));

evalV :: forall a b. Vexp a b -> (a -> Maybe b) -> Maybe b;
evalV (VConst v) sigma = Just v;
evalV (VName x) sigma = sigma x;

knot :: Maybe Bool -> Maybe Bool;
knot (Just b) = Just (not b);
knot Nothing = Nothing;

kimp :: Maybe Bool -> Maybe Bool -> Maybe Bool;
kimp p q =
  (if p == Just False || q == Just True then Just True
    else (if p == Just True && q == Just False then Just False else Nothing));

kand :: Maybe Bool -> Maybe Bool -> Maybe Bool;
kand p q =
  (if p == Just False || q == Just False then Just False
    else (if p == Just True && q == Just True then Just True else Nothing));

eval :: forall a b. (Eq b) => Expr a b -> (a -> Maybe b) -> Maybe Bool;
eval ETrue sigma = Just True;
eval EFalse sigma = Just False;
eval (EEq a b) sigma = (case evalV a sigma of {
                         Nothing -> Nothing;
                         Just u -> (case evalV b sigma of {
                                     Nothing -> Nothing;
                                     Just w -> Just (u == w);
                                   });
                       });
eval (ENot e) sigma = knot (eval e sigma);
eval (EAnd e_1 e_2) sigma = kand (eval e_1 sigma) (eval e_2 sigma);
eval (EOr e_1 e_2) sigma = kor (eval e_1 sigma) (eval e_2 sigma);
eval (EImp e_1 e_2) sigma = kimp (eval e_1 sigma) (eval e_2 sigma);
eval (EPresent x) sigma = Just (not (is_none (sigma x)));

sta :: forall a b c d e. (a -> Maybe b, (c, Event a d e)) -> a -> Maybe b;
sta (sigma, (tau, e)) = sigma;

st :: forall a b c d e.
        [(a -> Maybe b, (c, Event a d e))] -> Nat -> a -> Maybe b;
st pi j = sta (nth pi j);

inv_eval ::
  forall a b c d.
    (Eq b) => Inv a b -> [(a -> Maybe b, (Int, Event a c d))] -> Maybe Bool;
inv_eval (Always phi) pi =
  (if any (\ j -> eval phi (st pi j) == Just False)
        (upt zero_nat (size_list pi))
    then Just False else Nothing);
inv_eval (Eventually phi) pi =
  (if any (\ j -> eval phi (st pi j) == Just True) (upt zero_nat (size_list pi))
    then Just True else Nothing);
inv_eval (Next phi) pi =
  (if less_nat one_nat (size_list pi) then eval phi (st pi one_nat)
    else Nothing);

deadlines :: forall a b c d e. Sterm a b c d e -> [Deadline a];
deadlines (SMust s a (Just d)) = [d];
deadlines (SThen t u) = deadlines t ++ deadlines u;
deadlines (SOr t u) = deadlines t ++ deadlines u;
deadlines (SAnd t u) = deadlines t ++ deadlines u;
deadlines (SUnless t c u) = deadlines t ++ deadlines u;
deadlines (SMust v va Nothing) = [];
deadlines (SMustNot v va vb) = [];
deadlines (SMay v va vb) = [];
deadlines (SOnBreach v va) = [];

plus_int :: Int -> Int -> Int;
plus_int k l = Int_of_integer (integer_of_int k + integer_of_int l);

map_option :: forall a b. (a -> b) -> Maybe a -> Maybe b;
map_option f Nothing = Nothing;
map_option f (Just x2) = Just (f x2);

resolve ::
  forall a b.
    (a -> Maybe Int) -> Int -> (b -> Maybe a) -> Deadline b -> Maybe Int;
resolve ta tau_0 sigma_0 (DAt t) = Just t;
resolve t tau_0 sigma_0 (DAfter k) = Just (plus_int tau_0 k);
resolve t tau_0 sigma_0 (DFactor x k) =
  (case sigma_0 x of {
    Nothing -> Nothing;
    Just v -> map_option (\ ta -> plus_int ta k) (t v);
  });

activates ::
  forall a b c d e.
    (a -> Maybe Int) -> Int -> (b -> Maybe a) -> [Sterm b a c d e] -> Bool;
activates t tau_0 sigma_0 blk =
  all (\ ta ->
        all (\ d -> not (is_none (resolve t tau_0 sigma_0 d))) (deadlines ta))
    blk;

handler_bound ::
  forall a b c d e. (Eq c) => [Sterm a b c d e] -> Nat -> Maybe (Maybe Nat);
handler_bound blk i = (case nth blk i of {
                        SMust _ _ _ -> Nothing;
                        SMustNot _ _ _ -> Nothing;
                        SMay _ _ _ -> Nothing;
                        SThen _ _ -> Nothing;
                        SOr _ _ -> Nothing;
                        SAnd _ _ -> Nothing;
                        SUnless _ _ _ -> Nothing;
                        SOnBreach s _ -> Just (bound_to blk i s);
                      });

has_handler :: forall a b c d e. Sterm a b c d e -> Bool;
has_handler (SOnBreach s acts) = True;
has_handler (SThen t u) = has_handler t || has_handler u;
has_handler (SOr t u) = has_handler t || has_handler u;
has_handler (SAnd t u) = has_handler t || has_handler u;
has_handler (SUnless t c u) = has_handler t || has_handler u;
has_handler (SMust v va vb) = False;
has_handler (SMustNot v va vb) = False;
has_handler (SMay v va vb) = False;

less_eq_nat :: Nat -> Nat -> Bool;
less_eq_nat m n = integer_of_nat m <= integer_of_nat n;

wf_actions :: forall a b. [Baction a b] -> Bool;
wf_actions acts =
  not (null acts) && less_eq_nat (size_list (filter is_cont acts)) one_nat;

map_filter :: forall a b. (a -> Maybe b) -> [a] -> [b];
map_filter f [] = [];
map_filter f (x : xs) = (case f x of {
                          Nothing -> map_filter f xs;
                          Just y -> y : map_filter f xs;
                        });

wf_block :: forall a b c d e. (Eq c) => [Sterm a b c d e] -> Bool;
wf_block blk =
  all (\ i ->
        (case nth blk i of {
          SMust _ _ _ -> not (has_handler (nth blk i));
          SMustNot _ _ _ -> not (has_handler (nth blk i));
          SMay _ _ _ -> not (has_handler (nth blk i));
          SThen _ _ -> not (has_handler (nth blk i));
          SOr _ _ -> not (has_handler (nth blk i));
          SAnd _ _ -> not (has_handler (nth blk i));
          SUnless _ _ _ -> not (has_handler (nth blk i));
          SOnBreach s acts ->
            wf_actions acts && not (is_none (bound_to blk i s));
        }))
    (upt zero_nat (size_list blk)) &&
    distinct
      (map_filter
        (\ x ->
          (if not (is_none (handler_bound blk x))
            then Just (handler_bound blk x) else Nothing))
        (upt zero_nat (size_list blk)));

minus_int :: Int -> Int -> Int;
minus_int k l = Int_of_integer (integer_of_int k - integer_of_int l);

tstamp :: forall a b c d e. (a -> Maybe b, (c, Event a d e)) -> c;
tstamp (sigma, (tau, e)) = tau;

time :: forall a b c d. [(a -> Maybe b, (Int, Event a c d))] -> Nat -> Int;
time pi j = tstamp (nth pi j);

passed :: forall a b c d. Int -> [(a -> Maybe b, (Int, Event a c d))] -> Bool;
passed d pi = any (\ j -> less_int d (time pi j)) (upt zero_nat (size_list pi));

after :: Maybe Int -> Int -> Bool;
after Nothing tau = True;
after (Just l) tau = less_int l tau;

does :: forall a b c. (Eq a, Eq b) => a -> b -> Event c a b -> Bool;
does s a e = (case e of {
               Deontic sa aa _ -> sa == s && aa == a;
               Arrival _ -> False;
               Tick -> False;
             });

evt :: forall a b c d e. (a -> Maybe b, (c, Event a d e)) -> Event a d e;
evt (sigma, (tau, e)) = e;

acted ::
  forall a b c d.
    (Eq a,
      Eq b) => a -> b -> Maybe Int ->
                           Int -> [(c -> Maybe d, (Int, Event c a b))] -> Bool;
acted s a lo d pi =
  any (\ j ->
        does s a (evt (nth pi j)) &&
          after lo (time pi j) && less_eq_int (time pi j) d)
    (upt one_nat (size_list pi));

window ::
  forall a b c d.
    (Eq a,
      Eq b) => a -> b -> Maybe Int ->
                           Int ->
                             [(c -> Maybe d, (Int, Event c a b))] -> Verdict;
window s a lo d pi =
  (if acted s a lo d pi then Fulfilled
    else (if passed d pi then Breached d else Pending));

continue_after ::
  forall a b c d e.
    (Eq a,
      Eq b) => Int ->
                 a -> b -> Int ->
                             Int ->
                               Maybe (Baction a c) ->
                                 [(d -> Maybe e, (Int, Event d a b))] ->
                                   Continuation a;
continue_after tau_0 s a d tau_b (Just Terminate) pi = Terminated;
continue_after tau_0 s a d tau_b (Just (CureBy k)) pi =
  Cure (window s a (Just tau_b) (plus_int tau_b k) pi);
continue_after tau_0 sa a d tau_b (Just (EscalateTo s)) pi =
  Escalated s (window s a (Just tau_b) (plus_int tau_b (minus_int d tau_0)) pi);
continue_after tau_0 s a d tau_b Nothing pi = NoContinuation;
continue_after tau_0 s a d tau_b (Just (Notify va)) pi = NoContinuation;
continue_after tau_0 s a d tau_b (Just (Penalty va)) pi = NoContinuation;

cont_of :: forall a b. [Baction a b] -> Maybe (Baction a b);
cont_of acts = (case filter is_cont acts of {
                 [] -> Nothing;
                 c : _ -> Just c;
               });

handle_breach ::
  forall a b c d e.
    (Eq a,
      Eq b) => Int ->
                 a -> b -> Int ->
                             [Baction a c] ->
                               [(d -> Maybe e, (Int, Event d a b))] -> Status a;
handle_breach tau_0 s a d acts pi =
  (case window s a Nothing d pi of {
    Fulfilled -> SFulfilled;
    Breached tau_b ->
      SBreached tau_b (continue_after tau_0 s a d tau_b (cont_of acts) pi);
    Pending -> SPending;
  });

to_tm :: forall a b c d e. Sterm a b c d e -> Maybe (Tm a b c d);
to_tm (SMust s a d) = Just (TMust s a);
to_tm (SMustNot s a c) = Just (TMustNot s a c);
to_tm (SMay s a c) = Just (TMay s a c);
to_tm (SThen t u) = (case (to_tm t, to_tm u) of {
                      (Nothing, _) -> Nothing;
                      (Just _, Nothing) -> Nothing;
                      (Just ta, Just ua) -> Just (TThen ta ua);
                    });
to_tm (SOr t u) = (case (to_tm t, to_tm u) of {
                    (Nothing, _) -> Nothing;
                    (Just _, Nothing) -> Nothing;
                    (Just ta, Just ua) -> Just (TOr ta ua);
                  });
to_tm (SAnd t u) = (case (to_tm t, to_tm u) of {
                     (Nothing, _) -> Nothing;
                     (Just _, Nothing) -> Nothing;
                     (Just ta, Just ua) -> Just (TAnd ta ua);
                   });
to_tm (SUnless t c u) = (case (to_tm t, to_tm u) of {
                          (Nothing, _) -> Nothing;
                          (Just _, Nothing) -> Nothing;
                          (Just ta, Just ua) -> Just (TUnless ta c ua);
                        });
to_tm (SOnBreach s acts) = Nothing;

equal_outcome :: Outcome -> Outcome -> Bool;
equal_outcome Interrupted Violated = False;
equal_outcome Violated Interrupted = False;
equal_outcome Done Violated = False;
equal_outcome Violated Done = False;
equal_outcome Done Interrupted = False;
equal_outcome Interrupted Done = False;
equal_outcome Violated Violated = True;
equal_outcome Interrupted Interrupted = True;
equal_outcome Done Done = True;

equal_polarity :: Polarity -> Polarity -> Bool;
equal_polarity May MustNot = False;
equal_polarity MustNot May = False;
equal_polarity Must MustNot = False;
equal_polarity MustNot Must = False;
equal_polarity Must May = False;
equal_polarity May Must = False;
equal_polarity MustNot MustNot = True;
equal_polarity May May = True;
equal_polarity Must Must = True;

equal_event ::
  forall a b c. (Eq a, Eq b, Eq c) => Event a b c -> Event a b c -> Bool;
equal_event (Arrival x2) Tick = False;
equal_event Tick (Arrival x2) = False;
equal_event (Deontic x11 x12 x13) Tick = False;
equal_event Tick (Deontic x11 x12 x13) = False;
equal_event (Deontic x11 x12 x13) (Arrival x2) = False;
equal_event (Arrival x2) (Deontic x11 x12 x13) = False;
equal_event (Arrival x2) (Arrival y2) = x2 == y2;
equal_event (Deontic x11 x12 x13) (Deontic y11 y12 y13) =
  x11 == y11 && x12 == y12 && equal_polarity x13 y13;
equal_event Tick Tick = True;

nat_of_integer :: Integer -> Nat;
nat_of_integer k = Nat (max (0 :: Integer) k);

sorted_wrt :: forall a. (a -> a -> Bool) -> [a] -> Bool;
sorted_wrt p [] = True;
sorted_wrt p (x : ys) = all (p x) ys && sorted_wrt p ys;

is_trace ::
  forall a b c d e. (Linorder c) => [(a -> Maybe b, (c, Event a d e))] -> Bool;
is_trace pi = not (null pi) && sorted_wrt less_eq (map tstamp pi);

first_at ::
  forall a b c d e.
    (Eq b) => Expr a b -> [(a -> Maybe b, (c, Event a d e))] -> Nat -> Bool;
first_at c pi k =
  eval c (st pi k) == Just True &&
    all (\ j -> not (eval c (st pi j) == Just True)) (upt zero_nat k);

kappa :: Outcome -> Outcome;
kappa Done = Interrupted;
kappa Interrupted = Interrupted;
kappa Violated = Violated;

kors :: [Maybe Bool] -> Maybe Bool;
kors xs = foldr kor xs (Just False);

mem3 ::
  forall a b c d e.
    (Eq a, Eq b, Eq c, Eq d,
      Linorder e) => Tm a b c d ->
                       [(a -> Maybe b, (e, Event a c d))] ->
                         Outcome -> Maybe Bool;
mem3 (TMust s a) pi r =
  Just (is_trace pi &&
         equal_event (evt (last pi)) (Deontic s a Must) &&
           equal_outcome r Done);
mem3 (TMay s a c) pi r =
  Just (equal_outcome r Done &&
         (is_trace pi &&
            equal_event (evt (last pi)) (Deontic s a May) &&
              less_eq_nat one_nat (minus_nat (size_list pi) one_nat) &&
                eval c
                  (st pi
                    (minus_nat (size_list pi)
                      (nat_of_integer (2 :: Integer)))) ==
                  Just True ||
           equal_nat (size_list pi) one_nat));
mem3 (TMustNot s a c) pi r =
  Just (equal_outcome r Done && equal_nat (size_list pi) one_nat);
mem3 (TOr t u) pi r = kor (mem3 t pi r) (mem3 u pi r);
mem3 (TThen t u) pi r =
  kor (kors (map (\ k ->
                   kand (mem3 t (take (suc k) pi) Done) (mem3 u (drop k pi) r))
              (upt zero_nat (size_list pi))))
    (kand (mem3 t pi r) (Just (not (equal_outcome r Done))));
mem3 (TUnless t c u) pi r =
  kor (kand (mem3 t pi r)
        (Just (all (\ j -> not (eval c (st pi j) == Just True))
                (upt zero_nat (minus_nat (size_list pi) one_nat)))))
    (kors (map (\ k ->
                 (if first_at c pi k
                   then kand (ext3 t (take (suc k) pi))
                          (kors (map_filter
                                  (\ x ->
                                    (if equal_outcome (kappa x) r
                                      then Just (mem3 u (drop k pi) x)
                                      else Nothing))
                                  [Done, Interrupted, Violated]))
                   else Just False))
            (upt zero_nat (size_list pi))));
mem3 (TAnd t u) pi r = Nothing;

ext3 ::
  forall a b c d e.
    (Eq a, Eq b, Eq c, Eq d,
      Linorder e) => Tm a b c d ->
                       [(a -> Maybe b, (e, Event a c d))] -> Maybe Bool;
ext3 (TMust s a) rho = Just (is_trace rho);
ext3 (TMay s a c) rho =
  (if not (is_trace rho) then Just False
    else (if eval c (st rho (minus_nat (size_list rho) one_nat)) == Just True
           then Just True else Nothing));
ext3 (TMustNot s a c) rho = Just False;
ext3 (TOr t u) rho = kor (ext3 t rho) (ext3 u rho);
ext3 (TThen t u) rho =
  kor (ext3 t rho)
    (kors (map (\ k ->
                 kand (mem3 t (take (suc k) rho) Done) (ext3 u (drop k rho)))
            (upt zero_nat (size_list rho))));
ext3 (TUnless t c u) rho = (if not (is_trace rho) then Just False else Nothing);
ext3 (TAnd t u) rho = Nothing;

composite_line ::
  Nat ->
    Sterm [String] Atom String String Atom ->
      [([String] -> Maybe Atom, (Int, Event [String] String String))] -> Line;
composite_line n t pi =
  (case to_tm t of {
    Nothing -> LComposite n Nothing Nothing Nothing;
    Just u ->
      LComposite n (mem3 u pi Done) (mem3 u pi Interrupted)
        (mem3 u pi Violated);
  });

may_verdict ::
  forall a b c d.
    (Eq a, Eq b,
      Eq d) => a -> b -> Expr c d ->
                           [(c -> Maybe d, (Int, Event c a b))] -> Verdict;
may_verdict s a c pi =
  (if any (\ j ->
            does s a (evt (nth pi j)) &&
              eval c (st pi (minus_nat j one_nat)) == Just True)
        (upt one_nat (size_list pi))
    then Fulfilled else Pending);

forbidden ::
  forall a b c d.
    (Eq a, Eq b,
      Eq d) => a -> b -> Expr c d ->
                           [(c -> Maybe d, (Int, Event c a b))] -> Nat -> Bool;
forbidden s a c pi j =
  less_eq_nat one_nat j &&
    less_nat j (size_list pi) &&
      does s a (evt (nth pi j)) &&
        eval c (st pi (minus_nat j one_nat)) == Just True;

pr_verdict ::
  forall a b c d.
    (Eq a, Eq b,
      Eq d) => a -> b -> Expr c d ->
                           [(c -> Maybe d, (Int, Event c a b))] -> Verdict;
pr_verdict s a c pi =
  (case find (forbidden s a c pi) (upt zero_nat (size_list pi)) of {
    Nothing -> Pending;
    Just j -> Breached (time pi j);
  });

ob_verdict ::
  forall a b c d.
    (Eq a,
      Eq b) => a -> b -> Maybe Int ->
                           [(c -> Maybe d, (Int, Event c a b))] -> Verdict;
ob_verdict s a d pi =
  (case d of {
    Nothing ->
      (if any (\ j -> does s a (evt (nth pi j))) (upt one_nat (size_list pi))
        then Fulfilled else Pending);
    Just da -> window s a Nothing da pi;
  });

pr_actions ::
  forall a b c d e.
    (Eq c) => [Sterm a b c d e] -> Nat -> Verdict -> [Baction c e];
pr_actions blk i v =
  (case v of {
    Fulfilled -> [];
    Breached _ -> filter (\ x -> not (is_cont x)) (handler_of blk i);
    Pending -> [];
  });

time_of :: Atom -> Maybe Int;
time_of (ATime t) = Just t;
time_of (ABool v) = Nothing;
time_of (AInt v) = Nothing;
time_of (AStr v) = Nothing;

term_line ::
  Int ->
    ([String] -> Maybe Atom) ->
      [Sterm [String] Atom String String Atom] ->
        [([String] -> Maybe Atom, (Int, Event [String] String String))] ->
          Nat -> Line;
term_line tau_0 sigma_0 blk pi i =
  (case nth blk i of {
    SMust s a d ->
      (case bind d (resolve time_of tau_0 sigma_0) of {
        Nothing ->
          LMust (suc i) s a Nothing (case ob_verdict s a Nothing pi of {
                                      Fulfilled -> SFulfilled;
                                      Breached _ -> SPending;
                                      Pending -> SPending;
                                    });
        Just da ->
          LMust (suc i) s a (Just da)
            (handle_breach tau_0 s a da (handler_of blk i) pi);
      });
    SMustNot s a c -> let {
                        v = pr_verdict s a c pi;
                      } in LMustNot (suc i) s a v (pr_actions blk i v);
    SMay s a c -> LMay (suc i) s a (may_verdict s a c pi);
    SThen _ _ -> composite_line (suc i) (nth blk i) pi;
    SOr _ _ -> composite_line (suc i) (nth blk i) pi;
    SAnd _ _ -> composite_line (suc i) (nth blk i) pi;
    SUnless _ _ _ -> composite_line (suc i) (nth blk i) pi;
    SOnBreach s _ -> LOnBreach (suc i) s (map_option suc (bound_to blk i s));
  });

raw_trace ::
  [(Nd String Atom, (Int, Event [String] String String))] ->
    [([String] -> Maybe Atom, (Int, Event [String] String String))];
raw_trace obs = map (\ (d, (tau, e)) -> (flat d, (tau, e))) obs;

fd_name :: Fdecl -> String;
fd_name (Fdecl f t m) = f;

wt_fun ::
  forall a b c. (Eq c) => (a -> b -> Bool) -> Ty c a -> Maybe (Nd c b) -> Bool;
wt_fun i (TPrim q) v = (case v of {
                         Nothing -> False;
                         Just (Atom a) -> i q a;
                         Just (Nom _) -> False;
                       });
wt_fun i (TOptional t) v = (case v of {
                             Nothing -> True;
                             Just d -> wt_fun i t (Just d);
                           });
wt_fun i (TRecord fs) v =
  (case v of {
    Nothing -> False;
    Just (Atom _) -> False;
    Just (Nom m) -> all (\ (f, t) -> wt_fun i t (fmlookup m f)) fs;
  });

interp :: Prim -> Atom -> Bool;
interp PBool b = (case b of {
                   ABool _ -> True;
                   AInt _ -> False;
                   AStr _ -> False;
                   ATime _ -> False;
                 });
interp PInt b = (case b of {
                  ABool _ -> False;
                  AInt _ -> True;
                  AStr _ -> False;
                  ATime _ -> False;
                });
interp PStr b = (case b of {
                  ABool _ -> False;
                  AInt _ -> False;
                  AStr _ -> True;
                  ATime _ -> False;
                });
interp PTime b = (case b of {
                   ABool _ -> False;
                   AInt _ -> False;
                   AStr _ -> False;
                   ATime _ -> True;
                 });

fd_ty :: Fdecl -> Ty String Prim;
fd_ty (Fdecl f t m) = t;

ill_typed ::
  [Fdecl] ->
    [(Nd String Atom, (Int, Event [String] String String))] ->
      Maybe (Nat, String);
ill_typed fs obs =
  map_option (\ (j, x) -> (j, fd_name x))
    (find (\ (j, x) ->
            not (wt_fun interp (TOptional (fd_ty x))
                  (denaming (fd_name x) (fst (nth obs j)))))
      (concatMap (\ j -> map (\ a -> (j, a)) fs)
        (upt zero_nat (size_list obs))));

fd_age :: Fdecl -> Maybe Int;
fd_age (Fdecl f t m) = m;

max_age :: [Fdecl] -> String -> Maybe Int;
max_age fs f = (case find (\ x -> fd_name x == f) fs of {
                 Nothing -> Nothing;
                 Just a -> fd_age a;
               });

fresh ::
  forall a b c d.
    (Eq a, Eq c,
      Eq d) => Int -> a -> [(a -> Maybe b, (Int, Event a c d))] -> Nat -> Bool;
fresh m x pi j =
  any (\ i ->
        equal_event (evt (nth pi i)) (Arrival x) &&
          less_eq_int (minus_int (time pi j) (time pi i)) m)
    (upt zero_nat (suc j));

blockp ::
  forall a b c d.
    (Eq a, Eq c,
      Eq d) => (a -> Maybe Int) ->
                 [([a] -> Maybe b, (Int, Event [a] c d))] ->
                   Nat -> [a] -> Maybe b;
blockp m pi j p =
  (case p of {
    [] -> st pi j p;
    f : _ -> (case m f of {
               Nothing -> st pi j p;
               Just ma -> (if fresh ma [f] pi j then st pi j p else Nothing);
             });
  });

btrace ::
  forall a b c d.
    (Eq a, Eq c,
      Eq d) => (a -> Maybe Int) ->
                 [([a] -> Maybe b, (Int, Event [a] c d))] ->
                   [([a] -> Maybe b, (Int, Event [a] c d))];
btrace m pi =
  map (\ j -> (blockp m pi j, (time pi j, evt (nth pi j))))
    (upt zero_nat (size_list pi));

run ::
  Spec -> [(Nd String Atom, (Int, Event [String] String String))] -> [Line];
run sp obs =
  (case sp of {
    Spec fs blk invs ->
      let {
        pi = btrace (max_age fs) (raw_trace obs);
        tau_0 = time pi zero_nat;
        sigma_0 = st pi zero_nat;
      } in (if null obs || not (activates time_of tau_0 sigma_0 blk)
             then [LActivation False]
             else LActivation True :
                    (if not (wf_block blk) || not (cont_free_prohibitions blk)
                      then [LBlock False]
                      else LBlock True :
                             (case ill_typed fs obs of {
                               Nothing ->
                                 LTypes Nothing :
                                   map (term_line tau_0 sigma_0 blk pi)
                                     (upt zero_nat (size_list blk)) ++
                                     map (\ (n, iota) ->
   LInvariant n (inv_eval iota pi))
                                       invs;
                               Just e -> [LTypes (Just e)];
                             })));
  });

}
