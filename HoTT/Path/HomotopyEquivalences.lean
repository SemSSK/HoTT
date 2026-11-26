import HoTT.DataTypes.DataTypes
import HoTT.Path.PathFibrations


-- Homotopies are equivalences
def hom {P: A -> Type u} (f g: (x:A)-> P x)
:= ∀x, f x = g x

infix:50 " ~ " => hom

namespace hom

  def refl {P: A -> Type u} {f: (x:A)-> P x} : f ~ f
  := λ _ => Path.refl

  def symm {P: A -> Type u} {f g: (x:A)-> P x} :
  f ~ g -> g ~ f
  := λ homfg x => (homfg x).symm

  def trans {P: A -> Type u} {f g h: (x:A)-> P x} :
  f ~ g -> g ~ h -> f ~ h
  := λ homfg homgh x =>
    homfg x ▪ (homgh x)

  -- helpers
  def composition_assoc {A B C D: Type u} {f:A -> B} {g: B -> C} {h: C -> D} :
    h ∘ g ∘ f ~ (h ∘ g) ∘ f
  := λ _ => Path.refl

  def composition_left_id {f:A -> B} :
  f ~ id ∘ f
  := λ _ => Path.refl

  def composition_right_id {f:A -> B} :
  f ~ f ∘ id
  := λ _ => Path.refl
end hom



def hom_naturality {f g: A -> B} (x y: A) (H: f ~ g) (p: x = y) :
  (H x) ▪ (g ⋆ p) = (f ⋆ p) ▪ (H y)
:= let C := λ x y p => (H x) ▪ (g ⋆ p) = (f ⋆ p) ▪ (H y)
   let c := λ _ => trans_refl_right
   ind_path C c x y p



example {f: A -> A} {x: A} (H: f ~ id) :
  H (f x) = f ⋆ H x
:= let naturality := hom_naturality (f x) x H (H x);
 let t := (λ y => H (f x) ▪ y) ⋆ (ap_id_idempotent (H x))
 |>.symm.trans naturality;
 let t := (λ p => p ▪ (H x).symm) ⋆ t
 |>.symm.symm;
 let h := (path_trans_assoc).symm
 ▪ t
 ▪ path_trans_assoc;

  (path_trans_p_psymm).symm
  ▪ h
  ▪ path_trans_p_psymm


structure QInv (f: A -> B) where
  g: B -> A
  right_inv: f ∘ g ~ id
  left_inv: g ∘ f ~ id


example : QInv (id (α := A))
:= {
  g := id
  right_inv := λ _ => Path.refl
  left_inv := λ _ => Path.refl
}


def QInv.symm {f:A -> B} {qinv: QInv f} : QInv qinv.g
:= {
  g := f
  right_inv := qinv.left_inv
  left_inv := qinv.right_inv
}



example (x y z: A) (p: x = y) : QInv (p ▪ . : (y = z) -> (x = z))
:= QInv.mk (p.symm ▪ .)
  ( λ x =>
    let t : p ▪ p.symm = Path.refl := path_transitivity_left_inverse
    let t0 : p ▪ p.symm ▪ x = x :=
      path_trans_assoc.symm ▪
      (λ p => p ▪ x) ⋆ t;
    t0
  )
  (
    λ x =>
    let t : p.symm ▪ p = Path.refl := path_transitivity_right_inverse
    let t0 : p.symm ▪ p ▪ x = x :=
      path_trans_assoc.symm ▪
      (λ p => p ▪ x) ⋆ t;
    t0
  )


example (x y z: A) (p: x = y) : QInv (. ▪ p : (z = x) -> (z = y))
:= QInv.mk (. ▪ p.symm)
  (
    λ x =>
    let t : p.symm ▪ p = Path.refl := path_transitivity_right_inverse
    let t0 : x ▪ p.symm ▪ p = x :=
    (λ p => x ▪ p) ⋆ t
    |>.trans path_transitivity_right_identity.symm;
    path_trans_assoc ▪ t0
  )
  (
     λ x =>
    let t : p ▪ p.symm = Path.refl := path_transitivity_left_inverse
    let t0 : x ▪ p ▪ p.symm  = x :=
    (λ p => x ▪ p) ⋆ t
    |>.trans path_transitivity_right_identity.symm;
    path_trans_assoc ▪ t0
  )



-- transport P p.symm : P y -> P x
example (x y: A) (p: x = y) (P: A -> Type) : QInv (transport (P:=P) p)
:= QInv.mk (transport (P:=P) p.symm)
  (λ u =>
    let t0: transport (p.symm ▪ p) u = u :=
      (λ p => transport p u) ⋆ path_transitivity_right_inverse
    transport_dist_on_path_trans ▪ t0
  )
  (λ u =>
    let t0: transport (p ▪ p.symm) u = u :=
      (λ p => transport p u) ⋆ path_transitivity_left_inverse
    transport_dist_on_path_trans ▪ t0
  )


structure IsEquiv (f: A -> B) where
  g: B -> A
  right_inv: f ∘ g ~ id
  h: B -> A
  left_inv: h ∘ f ~ id

def QInv.into_IsEquiv {f: A -> B} (qinv: QInv f): IsEquiv f
:= {
  g := qinv.g
  right_inv := qinv.right_inv
  h := qinv.g
  left_inv := qinv.left_inv
}


def IsEquiv.into_QInv {f: A -> B} (isequiv: IsEquiv f): QInv f
:= {
  g := isequiv.g
  right_inv := isequiv.right_inv
  left_inv := (
    let step0 : (isequiv.h ∘ (f ∘ isequiv.g) ∘ f) ~ id
    := λ x => (
      let step0 : isequiv.h ∘ (f ∘ isequiv.g) ∘ f ~ isequiv.h ∘ (id) ∘ f
      := λ x =>  isequiv.h ⋆ (isequiv.right_inv (f x))
      let step1 : isequiv.h ∘ (id) ∘ f ~ id
      := λ x => isequiv.left_inv x
      step0.trans step1 x
    )
    let step1 : (isequiv.h ∘ (f ∘ isequiv.g) ∘ f) ~ isequiv.g ∘ f
    := λ x => (
      let step0 : isequiv.h ∘ f ∘ isequiv.g ~ (isequiv.h ∘ f) ∘ isequiv.g
      := hom.composition_assoc;
      let step1 : (isequiv.h ∘ f) ∘ isequiv.g ~ isequiv.g
      := λ x => isequiv.left_inv (isequiv.g x);
      (step0.trans step1) (f x)
    )
    step1.symm.trans step0
  )
}


structure TEquiv (A B: Type u) where
  f: A -> B
  proof_of_equiv: IsEquiv f

infix:50 " ≃ " => TEquiv



def TEquiv.refl {A: Type u} : A ≃ A
:= {
  f := id
  proof_of_equiv := {
    g := id
    right_inv := (Path.refl_ .)
    h := id
    left_inv := (Path.refl_ .)
  }
}

def TEquiv.symm {A B: Type u} {f: A ≃ B} : B ≃ A
:=
  let qinv :=  f.proof_of_equiv.into_QInv
  {
    f := qinv.g
    proof_of_equiv := qinv.symm.into_IsEquiv
  }

def TEquiv.trans {A B C: Type u} {f: A ≃ B} {g: B ≃ C} : A ≃ C
:=
  {
    f := g.f ∘ f.f
    proof_of_equiv := (
      let f_qinv := f.proof_of_equiv.into_QInv
      let g_qinv := g.proof_of_equiv.into_QInv
      let qinv : QInv (g.f ∘ f.f)
      := {
        g := f_qinv.g ∘ g_qinv.g
        right_inv := sorry
        left_inv := sorry
      }
      sorry
    )
  }
