
data Bool : Set where
  false : Bool
  true  : Bool

If : Set -> Set -> Bool -> Set
If x y true  = x
If x y false = y

if : (P : Bool -> Set) -> P true -> P false -> (b : Bool) -> P b
if P x y true  = x
if P x y false = y

data Sigma (A : Set)(B : A -> Set) : Set where
  wrap : [f : (b : Bool) -> If A (B (f true)) b] -> Sigma A B

fst : (A : Set) -> (B : A -> Set) -> Sigma A B -> A
fst A B (wrap f) = f true

snd : (A : Set) -> (B : A -> Set) -> (p : Sigma A B) -> B (fst A B p)
snd A B (wrap f) = f false

pair : (A : Set) -> (B : A -> Set) -> (x : A) -> (y : B x) -> Sigma A B
pair A B x y = wrap A B (if (If A (B x)) x y)

data Id (A : Set) (x : A) (y : A) : Set where
  eq : ((P : A -> Set) -> P x -> P y) -> Id A x y

refl : (A : Set) -> (x : A) -> Id A x x
refl A x = eq A x x (\P px -> px)

lemfst : (A : Set) -> (B : A -> Set) -> (x : A) -> (y : B x) -> Id A (fst A B (pair A B x y)) x
lemfst A B x y = refl A x

lemsnd : (A : Set) -> (B : A -> Set) -> (x : A) -> (y : B x) -> Id (B x) (snd A B (pair A B x y)) y
lemsnd A B x y = refl (B x) y

