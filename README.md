# HoTT 

Working through the HoTT book in Lean4

the tl;dr idea is to use a custom `Path` type instead of leans `Eq` type since lean treats it as Prop and apply proof irrelevance. The `Path` type being a Type allows me to have proof relevant for example : 

```lean
-- This is accepted 
example {x y: A} (p q: Eq x y): Eq p q
:= rfl

-- This is unprovable and is not accepted 
example {x y: A} (p q: Path x y) : Path p q
:= Path.refl
```

haven't thought of higher inductive types and other issues i might face 

another issue with this is that `Path` being a type means that it isn't erased at runtime and thus unideal for real code but this is a study work so it shouldn't be an issue 