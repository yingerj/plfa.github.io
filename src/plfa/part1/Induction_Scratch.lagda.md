Scratch: Where I play with things as I go, and copy code as I go so I can easily refrence it when working on exercises.

A trimmed down set of imports:
```agda
module plfa.part1.Induction_Scratch where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _+_)
```

# Revisting Rewrite

Rewrite didn't make too much sense to me so going back and playing with it.

## Getting to the problem with my understanding

The `+-assoc′` proof is given:

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ zero    n p                          =  refl
    +-assoc′ (suc m) n p  rewrite +-assoc′ m n p  =  refl

Now the type signature and the base case make plenty of sense, so just looking
at the inductive case.

When evaluating:
    +-assoc′ (suc m) n p = {!!}

The hole type is:
    suc m + n + p ≡ suc m + (n + p)

Given `suc` binds more tightly than `_+_` the following is equivalent:
    (suc m) + n + p ≡ (suc m) + (n + p)

Ok, but this doesn't look like what we see in `Induction.lagda.md` they're factoring `suc` out...
Hmm, does that rely on `+-suc` being defined? Nope, the rewrite works fine without it.

Ok, well what does the hole of this look like?
    +-assoc′ (suc m) n p  rewrite +-assoc′ m n p  = ?

It looks like this:
    suc (m + (n + p)) ≡ suc (m + (n + p))

Ok that wasn't what I was expecting, I was expecting no `suc`s.

```agda
+-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc′ zero    n p                          =  refl
+-assoc′ (suc m) n p  rewrite +-assoc′ m n p  =  refl
```


## Getting it Straight

Going back to PLFA Induction, I think this is the key bit:
    
    Rewriting replaces each occurrence of the left-hand side of the equation in the goal
    by the right-hand side.

This is really terse, let me try to flesh it out a bit:

    Rewriting replaces each occurrence of the left-hand side of the equation indicated
    by rewrite in the *goal* by the right-hand side of the equation indicated by rewrite.

So given that `+-assoc′` has the overall goal:
    (m + n) + p ≡ m + (n + p)

And `+-assoc′ (suc m) n p` has the concrete goal:
    suc m + n + p ≡ suc m + (n + p)
Equivalently:
    ((suc m) + n) + p ≡ (suc m) + (n + p)

Ah ok, I'd missed that the inductive case of`_+_` is used to simplify!

Inductive case:
    suc n + m = suc (n + m)

Simplification step by step:
    ((suc m) + n) + p ≡ (suc m) + (n + p)
    (suc (m + n)) + p ≡ (suc m) + (n + p)
    suc ((m + n) + p) ≡ (suc m) + (n + p)
    suc ((m + n) + p) ≡ suc (m + (n + p))

Ok, evidently Agda is able to do this simplification automatically. Or prehaps more
likely it stores expressions in a canonical form?

Anyways, with that simplificaiton understood, the rewrite is obvious:

    vvvvvvvvvvv To be Replaced in Goal's LHS
    (m + n) + p ≡ m + (n + p)
                  ^^^^^^^^^^^ Replacement

    suc ((m + n) + p) ≡ suc (m + (n + p))
         ^^^^^^^^^^^ Target of replacement

Resulting in:
    suc (m + (n + p)) ≡ suc (m + (n + p))

Ok, I think I've got rewrite figured out now.
