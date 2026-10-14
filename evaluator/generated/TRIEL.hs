{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  TRIEL(Int(..), integer_of_int, Nat, integer_of_nat, Num, Rat, quotient_of,
         Atom(..), Arg(..), Act(..), Fmap(..), Nd(..), Ty(..), Vexp(..),
         Expr(..), Verdict(..), Continuation(..), Status(..), Amount(..),
         Ract(..), Line(..), Prim(..), Deadline(..), Inv(..), Sinv(..),
         Baction(..), Sterm(..), Pexp(..), Pen(..), Fdecl(..), Spec(..),
         Polarity(..), Event(..), nat_of_integer, num_of, run, dec_atom)
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

equal_int :: Int -> Int -> Bool;
equal_int k l = integer_of_int k == integer_of_int l;

instance Eq Int where {
  a == b = equal_int a b;
};

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

times_nat :: Nat -> Nat -> Nat;
times_nat m n = Nat (integer_of_nat m * integer_of_nat n);

class Times a where {
  times :: a -> a -> a;
};

class (Times a) => Dvd a where {
};

instance Times Nat where {
  times = times_nat;
};

instance Dvd Nat where {
};

data Num = One | Bit0 Num | Bit1 Num;

one_nat :: Nat;
one_nat = Nat (1 :: Integer);

class One a where {
  one :: a;
};

instance One Nat where {
  one = one_nat;
};

plus_nat :: Nat -> Nat -> Nat;
plus_nat m n = Nat (integer_of_nat m + integer_of_nat n);

class Plus a where {
  plus :: a -> a -> a;
};

instance Plus Nat where {
  plus = plus_nat;
};

zero_nat :: Nat;
zero_nat = Nat (0 :: Integer);

class Zero a where {
  zero :: a;
};

instance Zero Nat where {
  zero = zero_nat;
};

class (Plus a) => Semigroup_add a where {
};

class (One a, Semigroup_add a) => Numeral a where {
};

instance Semigroup_add Nat where {
};

instance Numeral Nat where {
};

class (One a, Times a) => Power a where {
};

instance Power Nat where {
};

max :: forall a. (Ord a) => a -> a -> a;
max a b = (if less_eq a b then b else a);

instance Ord Integer where {
  less_eq = (\ a b -> a <= b);
  less = (\ a b -> a < b);
};

minus_nat :: Nat -> Nat -> Nat;
minus_nat m n = Nat (max (0 :: Integer) (integer_of_nat m - integer_of_nat n));

class Minus a where {
  minus :: a -> a -> a;
};

instance Minus Nat where {
  minus = minus_nat;
};

apsnd :: forall a b c. (a -> b) -> (c, a) -> (c, b);
apsnd f (x, y) = (x, f y);

divmod_integer :: Integer -> Integer -> (Integer, Integer);
divmod_integer k l =
  (if k == (0 :: Integer) then ((0 :: Integer), (0 :: Integer))
    else (if (0 :: Integer) < l
           then (if (0 :: Integer) < k then divMod (abs k) (abs l)
                  else (case divMod (abs k) (abs l) of {
                         (r, s) ->
                           (if s == (0 :: Integer)
                             then (negate r, (0 :: Integer))
                             else (negate r - (1 :: Integer), l - s));
                       }))
           else (if l == (0 :: Integer) then ((0 :: Integer), k)
                  else apsnd negate
                         (if k < (0 :: Integer) then divMod (abs k) (abs l)
                           else (case divMod (abs k) (abs l) of {
                                  (r, s) ->
                                    (if s == (0 :: Integer)
                                      then (negate r, (0 :: Integer))
                                      else (negate r - (1 :: Integer),
     negate l - s));
                                })))));

divide_integer :: Integer -> Integer -> Integer;
divide_integer k l = fst (divmod_integer k l);

divide_nat :: Nat -> Nat -> Nat;
divide_nat m n = Nat (divide_integer (integer_of_nat m) (integer_of_nat n));

class Divide a where {
  divide :: a -> a -> a;
};

instance Divide Nat where {
  divide = divide_nat;
};

modulo_integer :: Integer -> Integer -> Integer;
modulo_integer k l = snd (divmod_integer k l);

modulo_nat :: Nat -> Nat -> Nat;
modulo_nat m n = Nat (modulo_integer (integer_of_nat m) (integer_of_nat n));

class (Divide a, Dvd a) => Modulo a where {
  modulo :: a -> a -> a;
};

instance Modulo Nat where {
  modulo = modulo_nat;
};

less_eq_nat :: Nat -> Nat -> Bool;
less_eq_nat m n = integer_of_nat m <= integer_of_nat n;

less_nat :: Nat -> Nat -> Bool;
less_nat m n = integer_of_nat m < integer_of_nat n;

class (Semigroup_add a) => Cancel_semigroup_add a where {
};

class (Semigroup_add a) => Ab_semigroup_add a where {
};

class (Ab_semigroup_add a, Cancel_semigroup_add a,
        Minus a) => Cancel_ab_semigroup_add a where {
};

class (Semigroup_add a, Zero a) => Monoid_add a where {
};

class (Ab_semigroup_add a, Monoid_add a) => Comm_monoid_add a where {
};

class (Cancel_ab_semigroup_add a,
        Comm_monoid_add a) => Cancel_comm_monoid_add a where {
};

class (Times a, Zero a) => Mult_zero a where {
};

class (Times a) => Semigroup_mult a where {
};

class (Ab_semigroup_add a, Semigroup_mult a) => Semiring a where {
};

class (Comm_monoid_add a, Mult_zero a, Semiring a) => Semiring_0 a where {
};

class (Cancel_comm_monoid_add a, Semiring_0 a) => Semiring_0_cancel a where {
};

class (Semigroup_mult a) => Ab_semigroup_mult a where {
};

class (Ab_semigroup_mult a, Semiring a) => Comm_semiring a where {
};

class (Comm_semiring a, Semiring_0 a) => Comm_semiring_0 a where {
};

class (Comm_semiring_0 a,
        Semiring_0_cancel a) => Comm_semiring_0_cancel a where {
};

class (Semigroup_mult a, Power a) => Monoid_mult a where {
};

class (Monoid_mult a, Numeral a, Semiring a) => Semiring_numeral a where {
};

class (One a, Zero a) => Zero_neq_one a where {
};

class (Semiring_numeral a, Semiring_0 a, Zero_neq_one a) => Semiring_1 a where {
};

class (Semiring_0_cancel a, Semiring_1 a) => Semiring_1_cancel a where {
};

class (Ab_semigroup_mult a, Monoid_mult a, Dvd a) => Comm_monoid_mult a where {
};

class (Comm_monoid_mult a, Comm_semiring_0 a,
        Semiring_1 a) => Comm_semiring_1 a where {
};

class (Comm_semiring_0_cancel a, Comm_semiring_1 a,
        Semiring_1_cancel a) => Comm_semiring_1_cancel a where {
};

class (Linorder a, Comm_semiring_1_cancel a) => Interval a where {
};

instance Cancel_semigroup_add Nat where {
};

instance Ab_semigroup_add Nat where {
};

instance Cancel_ab_semigroup_add Nat where {
};

instance Monoid_add Nat where {
};

instance Comm_monoid_add Nat where {
};

instance Cancel_comm_monoid_add Nat where {
};

instance Mult_zero Nat where {
};

instance Semigroup_mult Nat where {
};

instance Semiring Nat where {
};

instance Semiring_0 Nat where {
};

instance Semiring_0_cancel Nat where {
};

instance Ab_semigroup_mult Nat where {
};

instance Comm_semiring Nat where {
};

instance Comm_semiring_0 Nat where {
};

instance Comm_semiring_0_cancel Nat where {
};

instance Monoid_mult Nat where {
};

instance Semiring_numeral Nat where {
};

instance Zero_neq_one Nat where {
};

instance Semiring_1 Nat where {
};

instance Semiring_1_cancel Nat where {
};

instance Comm_monoid_mult Nat where {
};

instance Comm_semiring_1 Nat where {
};

instance Comm_semiring_1_cancel Nat where {
};

instance Ord Nat where {
  less_eq = less_eq_nat;
  less = less_nat;
};

instance Preorder Nat where {
};

instance Order Nat where {
};

instance Linorder Nat where {
};

instance Interval Nat where {
};

class (Semiring_0 a) => Semiring_no_zero_divisors a where {
};

class (Semiring_1 a,
        Semiring_no_zero_divisors a) => Semiring_1_no_zero_divisors a where {
};

class (Comm_semiring_1_cancel a,
        Semiring_1_no_zero_divisors a) => Semidom a where {
};

instance Semiring_no_zero_divisors Nat where {
};

instance Semiring_1_no_zero_divisors Nat where {
};

instance Semidom Nat where {
};

class (One a, Zero a, Divide a) => Divide_trivial a where {
};

instance Divide_trivial Nat where {
};

class (Semiring_no_zero_divisors a) => Semiring_no_zero_divisors_cancel a where {
};

class (Divide_trivial a, Semidom a,
        Semiring_no_zero_divisors_cancel a) => Semidom_divide a where {
};

instance Semiring_no_zero_divisors_cancel Nat where {
};

instance Semidom_divide Nat where {
};

class (Comm_semiring_1_cancel a, Modulo a) => Semiring_modulo a where {
};

class (Divide_trivial a, Semiring_modulo a) => Semiring_modulo_trivial a where {
};

class (Semidom_divide a) => Algebraic_semidom a where {
};

class (Algebraic_semidom a,
        Semiring_modulo_trivial a) => Semidom_modulo a where {
};

instance Semiring_modulo Nat where {
};

instance Semiring_modulo_trivial Nat where {
};

instance Algebraic_semidom Nat where {
};

instance Semidom_modulo Nat where {
};

one_int :: Int;
one_int = Int_of_integer (1 :: Integer);

newtype Rat = Frct (Int, Int);

one_rat :: Rat;
one_rat = Frct (one_int, one_int);

instance One Rat where {
  one = one_rat;
};

times_int :: Int -> Int -> Int;
times_int k l = Int_of_integer (integer_of_int k * integer_of_int l);

quotient_of :: Rat -> (Int, Int);
quotient_of (Frct x) = x;

divide_int :: Int -> Int -> Int;
divide_int k l =
  Int_of_integer (divide_integer (integer_of_int k) (integer_of_int l));

uminus_int :: Int -> Int;
uminus_int k = Int_of_integer (negate (integer_of_int k));

zero_int :: Int;
zero_int = Int_of_integer (0 :: Integer);

gcd_int :: Int -> Int -> Int;
gcd_int (Int_of_integer x) (Int_of_integer y) =
  Int_of_integer (Prelude.gcd x y);

normalize :: (Int, Int) -> (Int, Int);
normalize p =
  (if less_int zero_int (snd p)
    then let {
           a = gcd_int (fst p) (snd p);
         } in (divide_int (fst p) a, divide_int (snd p) a)
    else (if equal_int (snd p) zero_int then (zero_int, one_int)
           else let {
                  a = uminus_int (gcd_int (fst p) (snd p));
                } in (divide_int (fst p) a, divide_int (snd p) a)));

times_rat :: Rat -> Rat -> Rat;
times_rat p q =
  Frct (case quotient_of p of {
         (a, c) -> (case quotient_of q of {
                     (b, d) -> normalize (times_int a b, times_int c d);
                   });
       });

instance Times Rat where {
  times = times_rat;
};

instance Power Rat where {
};

data Atom = ABool Bool | ANum Rat | AStr String | ATime Int;

data Arg = ArgName [String] | ArgVal Atom;

data Act = Act String [Arg];

equal_rat :: Rat -> Rat -> Bool;
equal_rat a b = quotient_of a == quotient_of b;

equal_atom :: Atom -> Atom -> Bool;
equal_atom (AStr x3) (ATime x4) = False;
equal_atom (ATime x4) (AStr x3) = False;
equal_atom (ANum x2) (ATime x4) = False;
equal_atom (ATime x4) (ANum x2) = False;
equal_atom (ANum x2) (AStr x3) = False;
equal_atom (AStr x3) (ANum x2) = False;
equal_atom (ABool x1) (ATime x4) = False;
equal_atom (ATime x4) (ABool x1) = False;
equal_atom (ABool x1) (AStr x3) = False;
equal_atom (AStr x3) (ABool x1) = False;
equal_atom (ABool x1) (ANum x2) = False;
equal_atom (ANum x2) (ABool x1) = False;
equal_atom (ATime x4) (ATime y4) = equal_int x4 y4;
equal_atom (AStr x3) (AStr y3) = x3 == y3;
equal_atom (ANum x2) (ANum y2) = equal_rat x2 y2;
equal_atom (ABool x1) (ABool y1) = x1 == y1;

equal_arg :: Arg -> Arg -> Bool;
equal_arg (ArgName x1) (ArgVal x2) = False;
equal_arg (ArgVal x2) (ArgName x1) = False;
equal_arg (ArgVal x2) (ArgVal y2) = equal_atom x2 y2;
equal_arg (ArgName x1) (ArgName y1) = x1 == y1;

instance Eq Arg where {
  a == b = equal_arg a b;
};

equal_act :: Act -> Act -> Bool;
equal_act (Act x1 x2) (Act y1 y2) = x1 == y1 && x2 == y2;

instance Eq Act where {
  a == b = equal_act a b;
};

instance Eq Atom where {
  a == b = equal_atom a b;
};

less_rat :: Rat -> Rat -> Bool;
less_rat p q =
  (case quotient_of p of {
    (a, c) -> (case quotient_of q of {
                (b, d) -> less_int (times_int a d) (times_int c b);
              });
  });

vless_atom :: Atom -> Atom -> Bool;
vless_atom (ANum p) (ANum q) = less_rat p q;
vless_atom (ABool v) uv = False;
vless_atom (AStr v) uv = False;
vless_atom (ATime v) uv = False;
vless_atom uu (ABool v) = False;
vless_atom uu (AStr v) = False;
vless_atom uu (ATime v) = False;

less_eq_rat :: Rat -> Rat -> Bool;
less_eq_rat p q =
  (case quotient_of p of {
    (a, c) -> (case quotient_of q of {
                (b, d) -> less_eq_int (times_int a d) (times_int c b);
              });
  });

vleq_atom :: Atom -> Atom -> Bool;
vleq_atom (ANum p) (ANum q) = less_eq_rat p q;
vleq_atom (ABool v) uv = False;
vleq_atom (AStr v) uv = False;
vleq_atom (ATime v) uv = False;
vleq_atom uu (ABool v) = False;
vleq_atom uu (AStr v) = False;
vleq_atom uu (ATime v) = False;

class Value_order a where {
  vless :: a -> a -> Bool;
  vleq :: a -> a -> Bool;
};

instance Value_order Atom where {
  vless = vless_atom;
  vleq = vleq_atom;
};

data Set a = Set [a] | Coset [a];

newtype Fmap a b = Fmap_of_list [(a, b)];

data Nd a b = Atom b | Nom (Fmap a (Nd a b));

data Ty a b = TPrim b | TOptional (Ty a b) | TRecord [(a, Ty a b)];

data Vexp a b = VConst b | VName a | VDefault a (Vexp a b);

data Expr a b = ETrue | EFalse | EEq (Vexp a b) (Vexp a b)
  | ELt (Vexp a b) (Vexp a b) | ELe (Vexp a b) (Vexp a b) | ENot (Expr a b)
  | EAnd (Expr a b) (Expr a b) | EOr (Expr a b) (Expr a b)
  | EImp (Expr a b) (Expr a b) | EPresent a;

data Tm a b c d = TMust c d | TMay c d (Expr a b) | TMustNot c d (Expr a b)
  | TThen (Tm a b c d) (Tm a b c d) | TOr (Tm a b c d) (Tm a b c d)
  | TUnless (Tm a b c d) (Expr a b) (Tm a b c d)
  | TAnd (Tm a b c d) (Tm a b c d) | TIf (Expr a b) (Tm a b c d) (Tm a b c d)
  | TSkip;

data Verdict = Fulfilled | Breached Int | Pending;

data Continuation a = NoContinuation | Terminated | Cure Verdict
  | Escalated a Verdict;

data Status a = SFulfilled | SPending | SBreached Int (Continuation a);

data Amount = PAmount Rat Bool | PUndefined | PNegative Rat;

data Ract a = RNotify a | RPenalty Amount;

data Line = LActivation Bool | LBlock Bool | LTypes (Maybe (Nat, String))
  | LMust Nat String Act (Maybe Int) (Status String) [Ract String]
  | LMustNot Nat String Act Verdict [Ract String] | LMay Nat String Act Verdict
  | LOnBreach Nat String (Maybe Nat)
  | LComposite Nat (Maybe Bool) (Maybe Bool) (Maybe Bool)
  | LInvariant String (Maybe Bool);

data Prim = PBool | PInt | PDec | PStr | PTime;

data Deadline a = DAt Int | DAfter Int | DFactor a Int;

data Inv a b = Always (Expr a b) | Eventually (Expr a b) | Next (Expr a b);

data Sinv a b = SInv (Inv a b) | SEventuallyWithin (Expr a b) (Deadline a);

data Baction a b = Notify a | Penalty b | Terminate | CureBy Int | EscalateTo a;

data Sterm a b c d e = SMust c d (Maybe (Deadline a)) (Maybe (Deadline a))
  | SMustNot c d (Expr a b) | SMay c d (Expr a b)
  | SThen (Sterm a b c d e) (Sterm a b c d e)
  | SOr (Sterm a b c d e) (Sterm a b c d e)
  | SAnd (Sterm a b c d e) (Sterm a b c d e)
  | SUnless (Sterm a b c d e) (Expr a b) (Sterm a b c d e)
  | SOnBreach c [Baction c e]
  | SIf (Expr a b) (Sterm a b c d e) (Sterm a b c d e) | SSkip | SRef Nat;

data Pexp a b = PVal (Vexp a b) | PAdd (Pexp a b) (Pexp a b)
  | PSub (Pexp a b) (Pexp a b) | PMul (Pexp a b) (Pexp a b) | PNeg (Pexp a b);

data Pen a b = Pen (Pexp a b) (Maybe Rat);

data Fdecl = Fdecl String (Ty String Prim) (Maybe Int);

data Spec =
  Spec [Fdecl] [Sterm [String] Atom String Act (Pen [String] Atom)]
    [(String, Sinv [String] Atom)];

data Polarity = Must | May | MustNot;

data Event a b c = Deontic b c Polarity | Arrival a | Tick;

data Outcome = Done | Interrupted | Violated;

nat_of_integer :: Integer -> Nat;
nat_of_integer k = Nat (max (0 :: Integer) k);

nat :: Int -> Nat;
nat = nat_of_integer . integer_of_int;

suc :: Nat -> Nat;
suc n = plus_nat n one_nat;

nth :: forall a. [a] -> Nat -> a;
nth (x : xs) n =
  (if equal_nat n zero_nat then x else nth xs (minus_nat n one_nat));

upt :: Nat -> Nat -> [Nat];
upt i j = (if less_nat i j then i : upt (suc i) j else []);

ball :: forall a. Set a -> (a -> Bool) -> Bool;
ball (Set xs) p = all p xs;

drop :: forall a. Nat -> [a] -> [a];
drop n [] = [];
drop n (x : xs) =
  (if equal_nat n zero_nat then x : xs else drop (minus_nat n one_nat) xs);

find :: forall a. (a -> Bool) -> [a] -> Maybe a;
find uu [] = Nothing;
find p (x : xs) = (if p x then Just x else find p xs);

fold :: forall a b. (a -> b -> b) -> [a] -> b -> b;
fold f [] s = s;
fold f (x : xs) s = fold f xs (f x s);

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

of_int :: Int -> Rat;
of_int a = Frct (a, one_int);

removeAll :: forall a. (Eq a) => a -> [a] -> [a];
removeAll x [] = [];
removeAll x (y : xs) = (if x == y then removeAll x xs else y : removeAll x xs);

membera :: forall a. (Eq a) => [a] -> a -> Bool;
membera [] y = False;
membera (x : xs) y = x == y || membera xs y;

inserta :: forall a. (Eq a) => a -> [a] -> [a];
inserta x xs = (if membera xs x then xs else x : xs);

insert :: forall a. (Eq a) => a -> Set a -> Set a;
insert x (Set xs) = Set (inserta x xs);
insert x (Coset xs) = Coset (removeAll x xs);

member :: forall a. (Eq a) => a -> Set a -> Bool;
member x (Set xs) = membera xs x;
member x (Coset xs) = not (membera xs x);

bind :: forall a b. Maybe a -> (a -> Maybe b) -> Maybe b;
bind Nothing f = Nothing;
bind (Just x) f = f x;

distinct :: forall a. (Eq a) => [a] -> Bool;
distinct [] = True;
distinct (x : xs) = not (membera xs x) && distinct xs;

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
binds sa (SMust s a d f) = s == sa;
binds sa (SMustNot s a c) = s == sa;
binds s (SMay v va vb) = False;
binds s (SThen v va) = False;
binds s (SOr v va) = False;
binds s (SAnd v va) = False;
binds s (SUnless v va vb) = False;
binds s (SOnBreach v va) = False;
binds s (SIf v va vb) = False;
binds s SSkip = False;
binds s (SRef v) = False;

bound_to ::
  forall a b c d e. (Eq c) => [Sterm a b c d e] -> Nat -> c -> Maybe Nat;
bound_to blk i s = let {
                     js = filter (\ j -> binds s (nth blk j)) (upt zero_nat i);
                   } in (if null js then Nothing else Just (last js));

handler_of ::
  forall a b c d e. (Eq c) => [Sterm a b c d e] -> Nat -> [Baction c e];
handler_of blk i =
  (case find (\ k -> (case nth blk k of {
                       SMust _ _ _ _ -> False;
                       SMustNot _ _ _ -> False;
                       SMay _ _ _ -> False;
                       SThen _ _ -> False;
                       SOr _ _ -> False;
                       SAnd _ _ -> False;
                       SUnless _ _ _ -> False;
                       SOnBreach s _ -> bound_to blk k s == Just i;
                       SIf _ _ _ -> False;
                       SSkip -> False;
                       SRef _ -> False;
                     }))
          (upt zero_nat (size_list blk))
    of {
    Nothing -> [];
    Just k -> (case nth blk k of {
                SMust _ _ _ _ -> [];
                SMustNot _ _ _ -> [];
                SMay _ _ _ -> [];
                SThen _ _ -> [];
                SOr _ _ -> [];
                SAnd _ _ -> [];
                SUnless _ _ _ -> [];
                SOnBreach _ acts -> acts;
                SIf _ _ _ -> [];
                SSkip -> [];
                SRef _ -> [];
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
          SMust _ _ _ _ -> True;
          SMustNot _ _ _ -> all (\ x -> not (is_cont x)) (handler_of blk k);
          SMay _ _ _ -> True;
          SThen _ _ -> True;
          SOr _ _ -> True;
          SAnd _ _ -> True;
          SUnless _ _ _ -> True;
          SOnBreach _ _ -> True;
          SIf _ _ _ -> True;
          SSkip -> True;
          SRef _ -> True;
        }))
    (upt zero_nat (size_list blk));

sinv_deadlines :: forall a b. Sinv a b -> [Deadline a];
sinv_deadlines (SInv iota) = [];
sinv_deadlines (SEventuallyWithin phi d) = [d];

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

inv_activates ::
  forall a b. (a -> Maybe Int) -> Int -> (b -> Maybe a) -> [Sinv b a] -> Bool;
inv_activates t tau_0 sigma_0 invs =
  all (\ iota ->
        all (\ d -> not (is_none (resolve t tau_0 sigma_0 d)))
          (sinv_deadlines iota))
    invs;

evalV :: forall a b. Vexp a b -> (a -> Maybe b) -> Maybe b;
evalV (VConst v) sigma = Just v;
evalV (VName x) sigma = sigma x;
evalV (VDefault x a) sigma = (case sigma x of {
                               Nothing -> evalV a sigma;
                               Just aa -> Just aa;
                             });

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

eval ::
  forall a b. (Eq b, Value_order b) => Expr a b -> (a -> Maybe b) -> Maybe Bool;
eval ETrue sigma = Just True;
eval EFalse sigma = Just False;
eval (EEq a b) sigma = (case evalV a sigma of {
                         Nothing -> Nothing;
                         Just u -> (case evalV b sigma of {
                                     Nothing -> Nothing;
                                     Just w -> Just (u == w);
                                   });
                       });
eval (ELt a b) sigma = (case evalV a sigma of {
                         Nothing -> Nothing;
                         Just u -> (case evalV b sigma of {
                                     Nothing -> Nothing;
                                     Just w -> Just (vless u w);
                                   });
                       });
eval (ELe a b) sigma = (case evalV a sigma of {
                         Nothing -> Nothing;
                         Just u -> (case evalV b sigma of {
                                     Nothing -> Nothing;
                                     Just w -> Just (vleq u w);
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
    (Eq b,
      Value_order b) => Inv a b ->
                          [(a -> Maybe b, (Int, Event a c d))] -> Maybe Bool;
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

tstamp :: forall a b c d e. (a -> Maybe b, (c, Event a d e)) -> c;
tstamp (sigma, (tau, e)) = tau;

time :: forall a b c d. [(a -> Maybe b, (Int, Event a c d))] -> Nat -> Int;
time pi j = tstamp (nth pi j);

passed :: forall a b c d. Int -> [(a -> Maybe b, (Int, Event a c d))] -> Bool;
passed d pi = any (\ j -> less_int d (time pi j)) (upt zero_nat (size_list pi));

ew_eval ::
  forall a b c d.
    (Eq b,
      Value_order b) => Expr a b ->
                          Int ->
                            [(a -> Maybe b, (Int, Event a c d))] -> Maybe Bool;
ew_eval phi d pi =
  (if any (\ j -> less_eq_int (time pi j) d && eval phi (st pi j) == Just True)
        (upt zero_nat (size_list pi))
    then Just True
    else (if passed d pi &&
               all (\ j ->
                     (if less_eq_int (time pi j) d
                       then eval phi (st pi j) == Just False else True))
                 (upt zero_nat (size_list pi))
           then Just False else Nothing));

sinv_eval ::
  forall a b c d.
    (Eq a,
      Value_order a) => (a -> Maybe Int) ->
                          Sinv b a ->
                            [(b -> Maybe a, (Int, Event b c d))] -> Maybe Bool;
sinv_eval t (SInv iota) pi = inv_eval iota pi;
sinv_eval t (SEventuallyWithin phi d) pi =
  (case resolve t (time pi zero_nat) (st pi zero_nat) d of {
    Nothing -> Nothing;
    Just da -> ew_eval phi da pi;
  });

deadlines :: forall a b c d e. Sterm a b c d e -> [Deadline a];
deadlines (SMust s a d f) = (case d of {
                              Nothing -> [];
                              Just da -> [da];
                            }) ++
                              (case f of {
                                Nothing -> [];
                                Just fa -> [fa];
                              });
deadlines (SThen t u) = deadlines t ++ deadlines u;
deadlines (SOr t u) = deadlines t ++ deadlines u;
deadlines (SAnd t u) = deadlines t ++ deadlines u;
deadlines (SUnless t c u) = deadlines t ++ deadlines u;
deadlines (SIf c t u) = deadlines t ++ deadlines u;
deadlines (SMustNot v va vb) = [];
deadlines (SMay v va vb) = [];
deadlines (SOnBreach v va) = [];
deadlines SSkip = [];
deadlines (SRef v) = [];

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
                        SMust _ _ _ _ -> Nothing;
                        SMustNot _ _ _ -> Nothing;
                        SMay _ _ _ -> Nothing;
                        SThen _ _ -> Nothing;
                        SOr _ _ -> Nothing;
                        SAnd _ _ -> Nothing;
                        SUnless _ _ _ -> Nothing;
                        SOnBreach s _ -> Just (bound_to blk i s);
                        SIf _ _ _ -> Nothing;
                        SSkip -> Nothing;
                        SRef _ -> Nothing;
                      });

has_handler :: forall a b c d e. Sterm a b c d e -> Bool;
has_handler (SOnBreach s acts) = True;
has_handler (SThen t u) = has_handler t || has_handler u;
has_handler (SOr t u) = has_handler t || has_handler u;
has_handler (SAnd t u) = has_handler t || has_handler u;
has_handler (SUnless t c u) = has_handler t || has_handler u;
has_handler (SIf c t u) = has_handler t || has_handler u;
has_handler (SMust v va vb vc) = False;
has_handler (SMustNot v va vb) = False;
has_handler (SMay v va vb) = False;
has_handler SSkip = False;
has_handler (SRef v) = False;

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
          SMust _ _ _ _ -> not (has_handler (nth blk i));
          SMustNot _ _ _ -> not (has_handler (nth blk i));
          SMay _ _ _ -> not (has_handler (nth blk i));
          SThen _ _ -> not (has_handler (nth blk i));
          SOr _ _ -> not (has_handler (nth blk i));
          SAnd _ _ -> not (has_handler (nth blk i));
          SUnless _ _ _ -> not (has_handler (nth blk i));
          SOnBreach s acts ->
            wf_actions acts && not (is_none (bound_to blk i s));
          SIf _ _ _ -> not (has_handler (nth blk i));
          SSkip -> not (has_handler (nth blk i));
          SRef _ -> not (has_handler (nth blk i));
        }))
    (upt zero_nat (size_list blk)) &&
    distinct
      (map_filter
        (\ x ->
          (if not (is_none (handler_bound blk x))
            then Just (handler_bound blk x) else Nothing))
        (upt zero_nat (size_list blk)));

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

sorted_wrt :: forall a. (a -> a -> Bool) -> [a] -> Bool;
sorted_wrt p [] = True;
sorted_wrt p (x : ys) = all (p x) ys && sorted_wrt p ys;

is_trace ::
  forall a b c d e. (Linorder c) => [(a -> Maybe b, (c, Event a d e))] -> Bool;
is_trace pi = not (null pi) && sorted_wrt less_eq (map tstamp pi);

first_at ::
  forall a b c d e.
    (Eq b,
      Value_order b) => Expr a b ->
                          [(a -> Maybe b, (c, Event a d e))] -> Nat -> Bool;
first_at c pi k =
  eval c (st pi k) == Just True &&
    all (\ j -> not (eval c (st pi j) == Just True)) (upt zero_nat k);

kappa :: Outcome -> Outcome;
kappa Done = Interrupted;
kappa Interrupted = Interrupted;
kappa Violated = Violated;

evt :: forall a b c d e. (a -> Maybe b, (c, Event a d e)) -> Event a d e;
evt (sigma, (tau, e)) = e;

kors :: [Maybe Bool] -> Maybe Bool;
kors xs = foldr kor xs (Just False);

mem3 ::
  forall a b c d e.
    (Eq a, Eq b, Value_order b, Eq c, Eq d,
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
mem3 (TIf c t u) pi r =
  (if null pi then Just False
    else (if eval c (st pi zero_nat) == Just True then mem3 t pi r
           else mem3 u pi r));
mem3 TSkip pi r =
  Just (equal_outcome r Done && equal_nat (size_list pi) one_nat);

ext3 ::
  forall a b c d e.
    (Eq a, Eq b, Value_order b, Eq c, Eq d,
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
ext3 (TIf c t u) rho =
  (if eval c (st rho zero_nat) == Just True then ext3 t rho else ext3 u rho);
ext3 TSkip rho = Just False;

composite_line ::
  Nat ->
    Maybe (Tm [String] Atom String Act) ->
      [([String] -> Maybe Atom, (Int, Event [String] String Act))] -> Line;
composite_line n t pi =
  (case t of {
    Nothing -> LComposite n Nothing Nothing Nothing;
    Just u ->
      LComposite n (mem3 u pi Done) (mem3 u pi Interrupted)
        (mem3 u pi Violated);
  });

does :: forall a b c. (Eq a, Eq b) => a -> b -> Event c a b -> Bool;
does s a e = (case e of {
               Deontic sa aa _ -> sa == s && aa == a;
               Arrival _ -> False;
               Tick -> False;
             });

may_verdict ::
  forall a b c d.
    (Eq a, Eq b, Eq d,
      Value_order d) => a -> b -> Expr c d ->
                                    [(c -> Maybe d, (Int, Event c a b))] ->
                                      Verdict;
may_verdict s a c pi =
  (if any (\ j ->
            does s a (evt (nth pi j)) &&
              eval c (st pi (minus_nat j one_nat)) == Just True)
        (upt one_nat (size_list pi))
    then Fulfilled else Pending);

zero_rat :: Rat;
zero_rat = Frct (zero_int, one_int);

uminus_rat :: Rat -> Rat;
uminus_rat p = Frct (case quotient_of p of {
                      (a, b) -> (uminus_int a, b);
                    });

minus_int :: Int -> Int -> Int;
minus_int k l = Int_of_integer (integer_of_int k - integer_of_int l);

minus_rat :: Rat -> Rat -> Rat;
minus_rat p q =
  Frct (case quotient_of p of {
         (a, c) ->
           (case quotient_of q of {
             (b, d) ->
               normalize
                 (minus_int (times_int a d) (times_int b c), times_int c d);
           });
       });

plus_rat :: Rat -> Rat -> Rat;
plus_rat p q =
  Frct (case quotient_of p of {
         (a, c) ->
           (case quotient_of q of {
             (b, d) ->
               normalize
                 (plus_int (times_int a d) (times_int b c), times_int c d);
           });
       });

lift2 :: (Rat -> Rat -> Rat) -> Maybe Rat -> Maybe Rat -> Maybe Rat;
lift2 f (Just x) (Just y) = Just (f x y);
lift2 f Nothing uv = Nothing;
lift2 f uu Nothing = Nothing;

evalP ::
  forall a b. (a -> Maybe Rat) -> Pexp b a -> (b -> Maybe a) -> Maybe Rat;
evalP num (PVal a) sigma = bind (evalV a sigma) num;
evalP num (PAdd p q) sigma =
  lift2 plus_rat (evalP num p sigma) (evalP num q sigma);
evalP num (PSub p q) sigma =
  lift2 minus_rat (evalP num p sigma) (evalP num q sigma);
evalP num (PMul p q) sigma =
  lift2 times_rat (evalP num p sigma) (evalP num q sigma);
evalP num (PNeg p) sigma = map_option uminus_rat (evalP num p sigma);

pen_amount ::
  forall a b. (a -> Maybe Rat) -> Pen b a -> (b -> Maybe a) -> Amount;
pen_amount num (Pen e cap) sigma =
  (case evalP num e sigma of {
    Nothing -> PUndefined;
    Just v ->
      (if less_rat v zero_rat then PNegative v
        else (case cap of {
               Nothing -> PAmount v False;
               Just c ->
                 (if less_rat c v then PAmount c True else PAmount v False);
             }));
  });

ract_of ::
  forall a b c.
    (a -> Maybe Rat) -> (b -> Maybe a) -> Baction c (Pen b a) -> [Ract c];
ract_of num sigma (Notify s) = [RNotify s];
ract_of num sigma (Penalty p) = [RPenalty (pen_amount num p sigma)];
ract_of num sigma Terminate = [];
ract_of num sigma (CureBy v) = [];
ract_of num sigma (EscalateTo v) = [];

report_actions ::
  forall a b c.
    (a -> Maybe Rat) -> (b -> Maybe a) -> [Baction c (Pen b a)] -> [Ract c];
report_actions num sigma acts = concatMap (ract_of num sigma) acts;

forbidden ::
  forall a b c d.
    (Eq a, Eq b, Eq d,
      Value_order d) => a -> b -> Expr c d ->
                                    [(c -> Maybe d, (Int, Event c a b))] ->
                                      Nat -> Bool;
forbidden s a c pi j =
  less_eq_nat one_nat j &&
    less_nat j (size_list pi) &&
      does s a (evt (nth pi j)) &&
        eval c (st pi (minus_nat j one_nat)) == Just True;

first_forbidden ::
  forall a b c d.
    (Eq a, Eq b, Eq d,
      Value_order d) => a -> b -> Expr c d ->
                                    [(c -> Maybe d, (Int, Event c a b))] -> Nat;
first_forbidden s a c pi =
  (case find (forbidden s a c pi) (upt zero_nat (size_list pi)) of {
    Nothing -> size_list pi;
    Just j -> j;
  });

pr_pen_state ::
  forall a b c d.
    (Eq a, Eq b, Eq d,
      Value_order d) => a -> b -> Expr c d ->
                                    [(c -> Maybe d, (Int, Event c a b))] ->
                                      c -> Maybe d;
pr_pen_state s a c pi = st pi (minus_nat (first_forbidden s a c pi) one_nat);

pr_verdict ::
  forall a b c d.
    (Eq a, Eq b, Eq d,
      Value_order d) => a -> b -> Expr c d ->
                                    [(c -> Maybe d, (Int, Event c a b))] ->
                                      Verdict;
pr_verdict s a c pi =
  (case find (forbidden s a c pi) (upt zero_nat (size_list pi)) of {
    Nothing -> Pending;
    Just j -> Breached (time pi j);
  });

pr_report ::
  forall a b c d.
    (Eq a, Value_order a, Eq b,
      Eq c) => (a -> Maybe Rat) ->
                 b -> c -> Expr d a ->
                             [Baction b (Pen d a)] ->
                               [(d -> Maybe a, (Int, Event d b c))] -> [Ract b];
pr_report num s a c acts pi =
  (case pr_verdict s a c pi of {
    Fulfilled -> [];
    Breached _ -> report_actions num (pr_pen_state s a c pi) acts;
    Pending -> [];
  });

after :: Maybe Int -> Int -> Bool;
after Nothing tau = True;
after (Just l) tau = less_int l tau;

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
                 Maybe Int ->
                   a -> b -> Int ->
                               [Baction a c] ->
                                 [(d -> Maybe e, (Int, Event d a b))] ->
                                   Status a;
handle_breach tau_0 lo s a d acts pi =
  (case window s a lo d pi of {
    Fulfilled -> SFulfilled;
    Breached tau_b ->
      SBreached tau_b (continue_after tau_0 s a d tau_b (cont_of acts) pi);
    Pending -> SPending;
  });

start_of ::
  forall a b.
    (a -> Maybe Int) ->
      Int -> (b -> Maybe a) -> Maybe (Deadline b) -> Maybe Int;
start_of t tau_0 sigma_0 f = (case f of {
                               Nothing -> Just tau_0;
                               Just a -> resolve t tau_0 sigma_0 a;
                             });

deadline_of ::
  forall a b.
    (a -> Maybe Int) ->
      Int ->
        (b -> Maybe a) -> Maybe (Deadline b) -> Maybe (Deadline b) -> Maybe Int;
deadline_of t tau_0 sigma_0 f d = (case start_of t tau_0 sigma_0 f of {
                                    Nothing -> Nothing;
                                    Just b -> bind d (resolve t b sigma_0);
                                  });

breach_entry ::
  forall a b c d. Int -> [(a -> Maybe b, (Int, Event a c d))] -> Nat;
breach_entry d pi =
  (case find (\ j -> less_int d (time pi j)) (upt zero_nat (size_list pi)) of {
    Nothing -> size_list pi;
    Just j -> j;
  });

ob_pen_state ::
  forall a b c d. Int -> [(a -> Maybe b, (Int, Event a c d))] -> a -> Maybe b;
ob_pen_state d pi = st pi (minus_nat (breach_entry d pi) one_nat);

ob_report ::
  forall a b c d.
    (a -> Maybe Rat) ->
      Int ->
        Status b ->
          [Baction b (Pen c a)] ->
            [(c -> Maybe a, (Int, Event c b d))] -> [Ract b];
ob_report num d sts acts pi =
  (case sts of {
    SFulfilled -> [];
    SPending -> [];
    SBreached _ _ -> report_actions num (ob_pen_state d pi) acts;
  });

ob_verdict ::
  forall a b c d.
    (Eq a,
      Eq b) => a -> b -> Maybe Int ->
                           Maybe Int ->
                             [(c -> Maybe d, (Int, Event c a b))] -> Verdict;
ob_verdict s a lo d pi =
  (case d of {
    Nothing ->
      (if any (\ j -> does s a (evt (nth pi j)) && after lo (time pi j))
            (upt one_nat (size_list pi))
        then Fulfilled else Pending);
    Just da -> window s a lo da pi;
  });

time_of :: Atom -> Maybe Int;
time_of (ATime t) = Just t;
time_of (ABool v) = Nothing;
time_of (ANum v) = Nothing;
time_of (AStr v) = Nothing;

lo_of :: forall a. Maybe (Deadline a) -> Int -> Maybe Int;
lo_of f b = (case f of {
              Nothing -> Nothing;
              Just _ -> Just (minus_int b one_int);
            });

num_of :: Atom -> Maybe Rat;
num_of (ANum q) = Just q;
num_of (ABool v) = Nothing;
num_of (AStr v) = Nothing;
num_of (ATime v) = Nothing;

must_line ::
  Int ->
    ([String] -> Maybe Atom) ->
      [Sterm [String] Atom String Act (Pen [String] Atom)] ->
        [([String] -> Maybe Atom, (Int, Event [String] String Act))] ->
          Nat ->
            String ->
              Act ->
                Maybe (Deadline [String]) -> Maybe (Deadline [String]) -> Line;
must_line tau_0 sigma_0 blk pi i s a d f =
  (case start_of time_of tau_0 sigma_0 f of {
    Nothing -> LMust (suc i) s a Nothing SPending [];
    Just b ->
      (case deadline_of time_of tau_0 sigma_0 f d of {
        Nothing ->
          LMust (suc i) s a Nothing
            (case ob_verdict s a (lo_of f b) Nothing pi of {
              Fulfilled -> SFulfilled;
              Breached _ -> SPending;
              Pending -> SPending;
            })
            [];
        Just da ->
          let {
            st = handle_breach b (lo_of f b) s a da (handler_of blk i) pi;
          } in LMust (suc i) s a (Just da) st
                 (ob_report num_of da st (handler_of blk i) pi);
      });
  });

to_tm_env ::
  forall a b c d e.
    [Maybe (Tm a b c d)] -> Sterm a b c d e -> Maybe (Tm a b c d);
to_tm_env gamma (SMust s a d f) = Just (TMust s a);
to_tm_env gamma (SMustNot s a c) = Just (TMustNot s a c);
to_tm_env gamma (SMay s a c) = Just (TMay s a c);
to_tm_env gamma (SThen t u) = (case (to_tm_env gamma t, to_tm_env gamma u) of {
                                (Nothing, _) -> Nothing;
                                (Just _, Nothing) -> Nothing;
                                (Just ta, Just ua) -> Just (TThen ta ua);
                              });
to_tm_env gamma (SOr t u) = (case (to_tm_env gamma t, to_tm_env gamma u) of {
                              (Nothing, _) -> Nothing;
                              (Just _, Nothing) -> Nothing;
                              (Just ta, Just ua) -> Just (TOr ta ua);
                            });
to_tm_env gamma (SAnd t u) = (case (to_tm_env gamma t, to_tm_env gamma u) of {
                               (Nothing, _) -> Nothing;
                               (Just _, Nothing) -> Nothing;
                               (Just ta, Just ua) -> Just (TAnd ta ua);
                             });
to_tm_env gamma (SUnless t c u) =
  (case (to_tm_env gamma t, to_tm_env gamma u) of {
    (Nothing, _) -> Nothing;
    (Just _, Nothing) -> Nothing;
    (Just ta, Just ua) -> Just (TUnless ta c ua);
  });
to_tm_env gamma (SIf c t u) = (case (to_tm_env gamma t, to_tm_env gamma u) of {
                                (Nothing, _) -> Nothing;
                                (Just _, Nothing) -> Nothing;
                                (Just ta, Just ua) -> Just (TIf c ta ua);
                              });
to_tm_env gamma SSkip = Just TSkip;
to_tm_env gamma (SRef k) =
  (if less_nat k (size_list gamma) then nth gamma k else Nothing);
to_tm_env gamma (SOnBreach s acts) = Nothing;

benv_from ::
  forall a b c d e.
    [Maybe (Tm a b c d)] -> [Sterm a b c d e] -> [Maybe (Tm a b c d)];
benv_from gamma [] = gamma;
benv_from gamma (t : ts) = benv_from (gamma ++ [to_tm_env gamma t]) ts;

benv :: forall a b c d e. [Sterm a b c d e] -> [Maybe (Tm a b c d)];
benv blk = benv_from [] blk;

term_line ::
  Int ->
    ([String] -> Maybe Atom) ->
      [Sterm [String] Atom String Act (Pen [String] Atom)] ->
        [([String] -> Maybe Atom, (Int, Event [String] String Act))] ->
          Nat -> Line;
term_line tau_0 sigma_0 blk pi i =
  (case nth blk i of {
    SMust a b c d -> must_line tau_0 sigma_0 blk pi i a b c d;
    SMustNot s a c ->
      LMustNot (suc i) s a (pr_verdict s a c pi)
        (pr_report num_of s a c (handler_of blk i) pi);
    SMay s a c -> LMay (suc i) s a (may_verdict s a c pi);
    SThen _ _ -> composite_line (suc i) (nth (benv blk) i) pi;
    SOr _ _ -> composite_line (suc i) (nth (benv blk) i) pi;
    SAnd _ _ -> composite_line (suc i) (nth (benv blk) i) pi;
    SUnless _ _ _ -> composite_line (suc i) (nth (benv blk) i) pi;
    SOnBreach s _ -> LOnBreach (suc i) s (map_option suc (bound_to blk i s));
    SIf _ _ _ -> composite_line (suc i) (nth (benv blk) i) pi;
    SSkip -> composite_line (suc i) (nth (benv blk) i) pi;
    SRef _ -> composite_line (suc i) (nth (benv blk) i) pi;
  });

raw_trace ::
  [(Nd String Atom, (Int, Event [String] String Act))] ->
    [([String] -> Maybe Atom, (Int, Event [String] String Act))];
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

floor_rat :: Rat -> Int;
floor_rat p = (case quotient_of p of {
                (a, b) -> divide_int a b;
              });

int_rat :: Rat -> Bool;
int_rat q = equal_rat (of_int (floor_rat q)) q;

dvd :: forall a. (Eq a, Semidom_modulo a) => a -> a -> Bool;
dvd a b = modulo b a == zero;

dec_den :: Nat -> Bool;
dec_den d =
  (if less_eq_nat d one_nat then equal_nat d one_nat
    else (if dvd (nat_of_integer (2 :: Integer)) d
           then dec_den (divide_nat d (nat_of_integer (2 :: Integer)))
           else (if dvd (nat_of_integer (5 :: Integer)) d
                  then dec_den (divide_nat d (nat_of_integer (5 :: Integer)))
                  else False)));

decimal :: Rat -> Bool;
decimal q = dec_den (nat (snd (quotient_of q)));

interp :: Prim -> Atom -> Bool;
interp PBool b = (case b of {
                   ABool _ -> True;
                   ANum _ -> False;
                   AStr _ -> False;
                   ATime _ -> False;
                 });
interp PInt b = (case b of {
                  ABool _ -> False;
                  ANum a -> int_rat a;
                  AStr _ -> False;
                  ATime _ -> False;
                });
interp PDec b = (case b of {
                  ABool _ -> False;
                  ANum a -> decimal a;
                  AStr _ -> False;
                  ATime _ -> False;
                });
interp PStr b = (case b of {
                  ABool _ -> False;
                  ANum _ -> False;
                  AStr _ -> True;
                  ATime _ -> False;
                });
interp PTime b = (case b of {
                   ABool _ -> False;
                   ANum _ -> False;
                   AStr _ -> False;
                   ATime _ -> True;
                 });

fd_ty :: Fdecl -> Ty String Prim;
fd_ty (Fdecl f t m) = t;

ill_typed ::
  [Fdecl] ->
    [(Nd String Atom, (Int, Event [String] String Act))] -> Maybe (Nat, String);
ill_typed fs obs =
  map_option (\ (j, x) -> (j, fd_name x))
    (find (\ (j, x) ->
            not (wt_fun interp (TOptional (fd_ty x))
                  (denaming (fd_name x) (fst (nth obs j)))))
      (concatMap (\ j -> map (\ a -> (j, a)) fs)
        (upt zero_nat (size_list obs))));

all_interval :: forall a. (Eq a, Interval a) => (a -> Bool) -> a -> a -> Bool;
all_interval p a b =
  (if less a b then p a && all_interval p (plus a one) b else True) &&
    (if a == b then p a else True);

sup_set :: forall a. (Eq a) => Set a -> Set a -> Set a;
sup_set (Set xs) a = fold insert xs a;
sup_set (Coset xs) a = Coset (filter (\ x -> not (member x a)) xs);

bot_set :: forall a. Set a;
bot_set = Set [];

refs :: forall a b c d e. Sterm a b c d e -> Set Nat;
refs (SRef k) = insert k bot_set;
refs (SThen t u) = sup_set (refs t) (refs u);
refs (SOr t u) = sup_set (refs t) (refs u);
refs (SAnd t u) = sup_set (refs t) (refs u);
refs (SUnless t c u) = sup_set (refs t) (refs u);
refs (SIf c t u) = sup_set (refs t) (refs u);
refs (SMust v va vb vc) = bot_set;
refs (SMustNot v va vb) = bot_set;
refs (SMay v va vb) = bot_set;
refs (SOnBreach v va) = bot_set;
refs SSkip = bot_set;

refs_ok :: forall a b c d e. [Sterm a b c d e] -> Bool;
refs_ok blk =
  let {
    d = minus_nat (size_list blk) one_nat;
  } in (if less_nat d (size_list blk)
         then all_interval
                (\ i ->
                  ball (refs (nth blk i))
                    (\ k -> less_nat k i && not (has_handler (nth blk k))))
                zero_nat d
         else True);

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

run :: Spec -> [(Nd String Atom, (Int, Event [String] String Act))] -> [Line];
run sp obs =
  (case sp of {
    Spec fs blk invs ->
      let {
        pi = btrace (max_age fs) (raw_trace obs);
        tau_0 = time pi zero_nat;
        sigma_0 = st pi zero_nat;
      } in (if null obs ||
                 (not (activates time_of tau_0 sigma_0 blk) ||
                   not (inv_activates time_of tau_0 sigma_0 (map snd invs)))
             then [LActivation False]
             else LActivation True :
                    (if not (wf_block blk) ||
                          (not (cont_free_prohibitions blk) ||
                            not (refs_ok blk))
                      then [LBlock False]
                      else LBlock True :
                             (case ill_typed fs obs of {
                               Nothing ->
                                 LTypes Nothing :
                                   map (term_line tau_0 sigma_0 blk pi)
                                     (upt zero_nat (size_list blk)) ++
                                     map (\ (n, iota) ->
   LInvariant n (sinv_eval time_of iota pi))
                                       invs;
                               Just e -> [LTypes (Just e)];
                             })));
  });

divide_rat :: Rat -> Rat -> Rat;
divide_rat p q =
  Frct (case quotient_of p of {
         (a, c) -> (case quotient_of q of {
                     (b, d) -> normalize (times_int a d, times_int c b);
                   });
       });

power :: forall a. (Power a) => a -> Nat -> a;
power a n =
  (if equal_nat n zero_nat then one
    else times a (power a (minus_nat n one_nat)));

dec_atom :: Int -> Nat -> Atom;
dec_atom m k =
  ANum (divide_rat (of_int m)
         (power (of_int (Int_of_integer (10 :: Integer))) k));

}
