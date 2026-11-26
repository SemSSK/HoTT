private inductive prePath {A: Type u} : A -> A -> Type u
| refl {a: A} : prePath a a

def Path {A: Type u} : A -> A -> Type u := prePath
def Path.refl {a: A} : Path a a := prePath.refl
def Path.refl_ (a: A) : Path a a := prePath.refl (a:=a)



def ind_path {A : Type u}
            (C: ∀x y, (p : Path x y) -> Sort v)
            (c:∀x, C x x Path.refl)
            (x y : A)
            (p : Path x y) :
            C x y p
:= match p with
  | prePath.refl => c x

infix:50 (priority := high) " = " => Path

#check (Path.refl_ 1)
