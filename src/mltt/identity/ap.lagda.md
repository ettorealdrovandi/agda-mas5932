---
title: "Identity types: ap" 
subtitle: "Martin-Löf Type Theory"
description: "A minimal Type Theory in Martin-Löf style: Identity types. Lemmmas on ap function"
---

```agda
{-# OPTIONS --without-K --safe #-}

module mltt.identity.ap where

open import level renaming (zero to lzero; suc to lsuc)
open import function.core
open import mltt.identity-types
open import mltt.identity.path-composition
```

```agda
module ap-lemmas where

  private
    variable
      ℓ ℓ' ℓ'' : Level
      A : Set ℓ
      B : Set ℓ'
      C : Set ℓ''
      x y z : A

  open ◾-lemmas

  ap◾ : (f : A → B) (p : x ≡ y) (q : y ≡ z) → ap f (p ◾ q) ≡ (ap f p) ◾ (ap f q)
  ap◾ f refl q = idp (ap f q)

  -- destruct q
  -- use reasoning
  ap◾' : (f : A → B) (p : x ≡ y) (q : y ≡ z) → ap f (p ◾ q) ≡ (ap f p) ◾ (ap f q)
  ap◾' f p refl = ap f (p ◾ refl) ≡⟨ ap (ap f) (ru p) ⟩
                  ap f p ≡⟨ ru (ap f p) ⁻¹ ⟩
                  (ap f p) ◾ refl ∎
    where
      open ≡-Reasoning

  ap◾′ : (f : A → B) (p : x ≡ y) (q : y ≡ z) → ap f (p ◾′ q) ≡ (ap f p) ◾′ (ap f q)
  ap◾′ f p refl = idp (ap f p)

  ap⁻¹ : (f : A → B) (p : x ≡ y) → ap f (p ⁻¹) ≡ (ap f p) ⁻¹
  ap⁻¹ f refl = refl

  ap∘ : (f : A → B) (g : B → C) (p : x ≡ y) →
        ap (g ∘′ f ) p ≡ ap g (ap f p)
  ap∘ f g refl = refl

  apid : (p : x ≡ y) → ap id p ≡ p
  apid refl = refl

  apconst : (p : x ≡ y) (b : B) → ap (λ (x : A) → b) p ≡ refl
  apconst refl b = refl
```

