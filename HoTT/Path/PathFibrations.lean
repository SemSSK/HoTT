import HoTT.DataTypes.DataTypes
import HoTT.Path.PathFunctoriality

-- Type families are fibrations
def transport  {P: A -> Type}  {x y: A} :  x = y -> P x -> P y
:= let C := λ x y _ => P x -> P y
  let c := λ _ => id
  ind_path C c x y

def lift_path {P: A -> Type} {x y: A} :
  (p: x = y) -> (u : P x) -> (DepPair.intro x u) = ⟨y,transport p u⟩
:= let C := λ x y p =>
  (u: P x) -> (DepPair.intro x u) = ⟨y, transport p u⟩
 let c := λ _ _ => Path.refl
 ind_path C c x y


def apd {P: A -> Type} {x y : A} (f: ∀ a, P a):
  (p: x = y) -> (transport p (f x)) = (f y)
:=  let C := λ x y p => (transport p (f x)) = (f y);
    let c := λ _ => Path.refl;
    ind_path C c x y


def constant_P (A B : Type) : A -> Type := fun _ => B

def transportconst {A B: Type} {x y: A} :
  (p: x = y) -> (b: constant_P A B x) -> (transport p b) = b
:=
  let C : ∀ x y: A, (p: x = y) -> Type :=
    λ x (_: A) p => (b: constant_P A B x) -> (transport p b) = b;
  let c := λ _ _ => Path.refl;
  ind_path C c x y

-- lemma 2.3.8
example {f: A -> B} {x y: A} :
  (p: x = y) ->
  (apd f p) =
  (transportconst p (f x) ▪ (ap f p))
:= let C := λ x _ p =>
  (apd f p) = (transportconst p (f x) ▪ (ap f p))
   let c := λ _ => Path.refl
   ind_path C c x y


-- lemma 2.3.9
def transport_dist_on_path_trans {P: A -> Type} {x y z: A}
  {p: x = y}
  {q: y = z}
  {u: P x} :
  (transport q (transport p u)) = (transport (p ▪ q) u)
:= let C := λ x y p =>
  (q: y = z) ->
  (u: P x) ->
  (transport q (transport p u)) = (transport (p ▪ q) u)
  let c := λ _ _ _ => Path.refl
  ind_path C c x y p q u


-- lemma 2.3.10
example {f: A -> B} {P: B -> Type} {x y: A} :
  (p: x = y) ->
  (u: P (f x) ) ->
  (transport (P:= P∘f) p u) = (transport (P:=P) (f ⋆ p) u)
:= let C : ∀x (y:A) (_:Path x y), Type := λ x _ p =>
  (u: P (f x) ) ->
  (transport (P:= P∘f) p u) = (transport (P:=P) (f ⋆ p) u)
  let c : ∀(x:A), C x x Path.refl := λ _ _ => Path.refl
  ind_path C c x y


-- lemma 2.3.11
example {P Q: A -> Type} {f: ∀x, P x -> Q x} {x y: A} :
  (p: x = y) ->
  (u: P x) ->
  (transport (P:=Q) p (f x u)) = (f y (transport (P:=P) p u))
:= let C := λ x y p =>
  (u: P x) ->
  (transport (P:=Q) p (f x u)) = (f y (transport (P:=P) p u))
  let c := λ _ _ => Path.refl
  ind_path C c x y
