import HoTT.Path.Path


-- Types are higher groupoids


def Path.symm {A: Type u} {a b: A} : a = b -> b = a
:= let C := λ x y _ => y = x;
   let c : ∀x, C x x Path.refl := λ _ => Path.refl;
   ind_path C c a b

def Path.trans {A: Type u} {a b c: A}: a = b -> b = c -> a = c
:= λ p q =>
  let C := λ x y _ => ∀z, y = z -> x = z
  let d := λ _ _ q => q
  ind_path C d a b p c q

infixr:80 " ▪ " => Path.trans

def trans_refl_right {A : Type u} {a b : A}
  {p : a = b} :
  p ▪ Path.refl = p
:= let C := λ _ _  p => p ▪ Path.refl = p
  let c := λ _ => Path.refl
  ind_path C c a b p




def path_transitivity_right_identity {A: Type u} {a b: A}
  {p: a = b} :
  p = p ▪ Path.refl
:= let C := λ _ _ p => p = (p.trans Path.refl);
   let c : ∀x, C x x Path.refl := λ _ => Path.refl
   ind_path C c a b p

def path_transitivity_left_identity {A: Type u} {a b: A} :
  (p: a = b) ->
  p ▪ Path.refl = p
:= let C := λ _ _ p => p ▪ Path.refl = p;
   let c := λ _ => Path.refl;
   ind_path C c a b

def path_transitivity_right_inverse {A: Type u} {a b: A}
  {p: a = b} :
  p.symm ▪ p = Path.refl
:= let C := λ _ _ p => p.symm ▪ p = Path.refl ;
   let c := λ _ => Path.refl;
   ind_path C c a b p

def path_transitivity_left_inverse {A: Type u} {a b: A}
  {p: a = b} :
  p ▪ p.symm = Path.refl
:= let C := λ _ _ p => p ▪ p.symm = Path.refl;
   let c := λ _ => Path.refl;
   ind_path C c a b p

def path_symm_involutive {A: Type u} {a b: A}:
  (p: a = b) ->
  p.symm.symm = p
:= let C := λ _ _ p => p.symm.symm = p;
   let c := λ _ => Path.refl;
   ind_path C c a b


private def path_trans_assoc' {A: Type u} {a b: A}:
  (p: a = b) ->
  {c d: A} ->
  (q: b = c) ->
  (r: c = d) ->
  (p ▪ q) ▪ r = p ▪ q ▪ r
:= let C := λ _ b p => {c d: A} ->
  (q: b = c) ->
  (r: c = d) ->
  (p ▪ q) ▪ r = p ▪ q ▪ r;
   let c := λ _ _ _ _ _ => Path.refl;
   ind_path C c a b

def path_trans_assoc {A: Type u} {a b c d: A}
  {p: a = b}
  {q: b = c}
  {r: c = d} :
  (p ▪ q) ▪ r = p ▪ (q ▪ r)
:= path_trans_assoc' p q r



def path_trans_p_psymm {A: Type u} {a b c: A}
  {p: a = b}
  {q: b = c} :
  p ▪ q ▪ q.symm = p
:=
  let D := λ (x y: A) (p: x = y) =>
  (z: A) ->
  (q: y = z) ->
  p ▪ q ▪ q.symm = p;
  let d : (x: A) -> D x x Path.refl := λ _ _ _ => path_transitivity_left_inverse
  (ind_path D d a b p) c q
