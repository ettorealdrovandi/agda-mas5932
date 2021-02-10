---
title: "Identity types: path composition"
subtitle: "Martin-Löf Type Theory"
description: "A minimal Type Theory in Martin-Löf style: Identity types. Path composition lemmmas"
---

```agda
{-# OPTIONS --without-K --safe #-}

module mltt.identity.path-composition where

open import level renaming (zero to lzero; suc to lsuc)
open import function.core
open import mltt.identity-types
```

### Lemmas about _◾_ (path composition)

```agda
module ◾-lemmas where

  private
    variable
      ℓ : Level
      A : Set ℓ
      x y : A

  -- refl is a left-unit
  lu : (p : x ≡ y) → idp (lhs p) ◾ p ≡ p
  lu p = idp p

  -- refl is a right-unit
  ru : (p : x ≡ y) → p ◾ idp (rhs p) ≡ p
  ru refl = refl

  lu=ru : {x : A} → lu (idp x) ≡ ru (idp x)
  lu=ru = idp (refl)

  -- right inverse
  rinv : (p : x ≡ y) → p ◾ p ⁻¹ ≡ idp (lhs p)
  rinv refl = refl

  -- left inverse
  linv : (p : x ≡ y) → p ⁻¹ ◾ p ≡ idp (rhs p)
  linv refl = refl

  -- taking the inverse twice is the identity
  inv²-id : (p : x ≡ y) → (p ⁻¹) ⁻¹ ≡ p
  inv²-id {x = x} refl = idp (refl {x = x})

  -- composition is associative
  assoc : {z w : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) → (p ◾ q) ◾ r ≡ p ◾ (q ◾ r)
  assoc refl q r = idp (q ◾ r)
```
