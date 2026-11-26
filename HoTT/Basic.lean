import HoTT.Path.Path

example {x y: A} (p q: Eq x y): Eq p q
:= rfl

example {x y: A} (p q: Path x y) : Path p q
:= Path.refl
