---
title: "Function: pointwise equality"
description: "Pointwise equality of functions"
---


```agda
{-# OPTIONS --without-K --safe #-}

module function.pointwise where

open import level
open import function.core
open import mltt.identity.core
```

The relation `f ~ g` means that for any point the values of f and g are propositionally equal. Interpreting the propositional equality as a path in the target type, this is a pointwise homotopy.

```agda
infix 3 _~_
_~_ : ∀ {ℓ ℓ'} {A : Set ℓ}{P : A → Set ℓ'} (f g : (x : A) → P x) → Set (ℓ ⊔ ℓ')
_~_ {ℓ} {ℓ'} {A} {P} f g = (x : A) → (f x) ≡ (g x)
```

```agda
module ~-lemmas {ℓ ℓ' : Level} {A : Set ℓ}  where

  private
    variable
      P : A → Set ℓ'

  -- Reflexive
  ~-refl : {f : (x : A) → P x} → (f ~ f)
  ~-refl  = λ x → refl


  -- Symmetric
  ~-sym : {f g : (x : A) → P x} → (f ~ g) → (g ~ f)
  ~-sym p = λ x → (p x) ⁻¹

  syntax ~-sym p = p ~⁻¹


  -- Transitive
  ~-trans : {f g h : (x : A) → P x} → (f ~ g) → (g ~ h) → (f ~ h)
  ~-trans p q = λ x → (p x) ◾ (q x)

  syntax ~-trans p q = p ~◾~ q


  -- Precomposition
  ~-comp : ∀ {i} {X : Set i} {f g : (x : A) → P x} → f ~ g → (h : X → A) → 
            (f ∘ h) ~ (g ∘ h)
  ~-comp p h = λ x → p (h x)

  syntax ~-comp p h = p ~∘ h

  -- Non-dependent composition
  ap-~ : ∀ {ℓ''} {B : Set ℓ'} {C : Set ℓ''} (h : B → C) {f g : A → B} →
         (p : f ~ g) → (h ∘′ f) ~ (h ∘′ g)
  ap-~ h p = λ x → ap h (p x)

  syntax ap-~ h p = h ∘~ p

  -- dependent composition
  apd-~ : ∀ {ℓ''} {C : {x : A} → P x → Set ℓ''}
          (h : {x : A} (y : P x) → C y) {f g : (x : A) → P x} →
          (p : f ~ g) →
          (λ (x : A) → (transport (λ (y : P x) → C {x} y) (p x)) ((h ∘ f) x) ) ~ (h ∘ g)
  apd-~ h p = λ x → apd h (p x)
```

