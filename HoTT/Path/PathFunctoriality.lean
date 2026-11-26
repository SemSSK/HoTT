import HoTT.Path.Path
import HoTT.Path.PathGroupoid


-- Functions are functors
def ap (f: A -> B) : (x = y) -> f x = f y
:= let C  := λ x y _ => f x = f y;
   let c := λ _ => Path.refl;
   ind_path C c x y



infixr:80 " ⋆ " => ap


def ap_dist_on_path_trans {f: A -> B} {x y z : A} :
  (p: x = y) -> (q: y = z) ->
  f ⋆ (p ▪ q) = (f ⋆ p) ▪ f ⋆ q
:= let C := λ _ y p => (q: y = z) ->
  f ⋆ (p ▪ q) = (f ⋆ p) ▪ f ⋆ q
  let c := λ _ _ => Path.refl
  ind_path C c x y

def ap_symm_eq_symm_ap {f: A -> B} {x y : A} :
  (p: x = y) ->
  f ⋆ p.symm = (f ⋆ p).symm
:= let C := λ _ _ p => (f ⋆ p.symm) = (f ⋆ p).symm
  let c := λ _ => Path.refl
  ind_path C c x y

def ap_on_ap_eq_ap_on_compose  {f: A -> B} {g: B -> A} {x y : A} :
  (p: x = y) ->
  g ⋆ f ⋆ p = (g ∘ f) ⋆ p
:= let C := λ _ _ p => g ⋆ f ⋆ p = (g ∘ f) ⋆ p
  let c := λ _ => Path.refl
  ind_path C c x y

def ap_id_idempotent {x y : A}:
 (p: x = y) ->
 id ⋆ p = p
:= let C := λ _ _ p => id ⋆ p = p
  let c := λ _ => Path.refl
  ind_path C c x y
