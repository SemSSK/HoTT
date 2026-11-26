
-- Dependent Pair
inductive DepPair (X: Type) (P: X -> Type) : Type where
| intro: (x: X) -> (u:P x) -> DepPair X P


def rec_depPair {X: Type} {P: X -> Type} :
  ((x: X) -> (u:P x) -> Y) ->
  (DepPair X P) -> Y
:= λ g ⟨x,u⟩ => g x u

def ind_depPair {X: Type} {P: X -> Type}
  (C: DepPair X P -> Type)
  (c: (x: X) -> (u:P x) -> C ⟨x,u⟩)
  (p: DepPair X P) :
  C p
:= match p with
  | ⟨x,u⟩ => c x u


def DepPair.fst : DepPair X P -> X
:= let g := λ x _ => x;
   rec_depPair g

def DepPair.snd : (p: DepPair X P) -> P (p.fst)
:= let C := λ (p: DepPair X P) => P (p.fst);
  let c := λ _ u => u
  ind_depPair C c
