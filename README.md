infernalize
===
A dependently typed language in which type inference is internalized into the
object language.
Dependent types usually internalize type checking, via the type `Type`, and
sometimes internalize type equality, via the identity type, but I've never seen
one internalize type inference.
This language does, and appears to have applications in defining type abstract,
and is related to syntax sugar.

The key rules are:

```
Γ ⊢ e : A
-------------------
Γ ⊢ infer e : Type

Γ ⊢ e : A
----------------
Γ ⊢ infer e ≡ A
```
