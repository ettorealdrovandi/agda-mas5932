---
title: "Function: Homotopy equivalences"
description: "Functions that admit a quasi-inverse"
---

```agda
{-# OPTIONS --without-K --safe #-}

module function.homotopyequivalence where

open import level
open import function.core
open import function.pointwise
open import mltt.sigma
open import mltt.identity.core
```

In Topology we say that a map $f \colon X → Y$ is a *homotopy equivalence* if there exists a $g \colon Y → X$ such that $f ∘ g ∼ \mathrm{id}_Y$ and $g ∘ f ∼ \mathrm{id}_X$. We say that $g$ is a *quasi-inverse* to $f$. We implement this notion by defining the *type* of quasi-inverses of `f : A → B`. 

This type is implemented as a record following the [Agda-base library](https://github.com/pcapriotti/agda-base.git) with conversions to the sigma types.

```agda
record qinv {ℓ ℓ' : Level} {A : Set ℓ} {B : Set ℓ'} (f : A → B) : Set (ℓ ⊔ ℓ') where
  field
    inv : B → A
    ε : f ∘′ inv ~ id
    η : inv ∘′ f ~ id
```

```agda
record _≅_ {ℓ ℓ' : Level} (A : Set ℓ) (B : Set ℓ') : Set (ℓ ⊔ ℓ') where
  constructor hoeq
  field
    to : A → B
    from : B → A  
    ε : to ∘′ from ~ id
    η : from ∘′ to ~ id


≅-struct-iso : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} →
               (A ≅ B) ≅ (Σ[ f ∈ (A → B) ] 
                          Σ[ g ∈ (B → A) ] ((f ∘′ g ~ id) × (g ∘′ f ~ id)) )
≅-struct-iso = record { to = λ { (hoeq f g ε η) → f , g , (ε , η)}
                      ; from = λ { (f , g , ε , η) → hoeq f g ε η}
                      ; ε = λ _ → refl
                      ; η = λ _ → refl }

qinv-struct-iso : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'}
                  (f : A → B) → (qinv f) ≅ 
                                (Σ[ g ∈ (B → A) ] ((f ∘′ g ~ id) × (g ∘′ f ~ id)))
qinv-struct-iso f = record { to = λ { record { inv = g ; ε = ε ; η = η } → g , (ε , η)}
                           ; from = λ { (g , ε , η) → record { inv = g ; ε = ε ; η = η } }
                           ; ε = λ x → refl
                           ; η = λ x → refl }
```

```agda
module ≅-lemmas where

  refl≅ : ∀ {ℓ} {A : Set ℓ} → A ≅ A
  refl≅ = hoeq (λ z → z) (λ z → z) (λ x → refl) (λ x → refl)

  ≡→≅ : ∀ {ℓ} {A B : Set ℓ} → A ≡ B → A ≅ B
  ≡→≅ refl = refl≅

  ≅-sym : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} →
          A ≅ B → B ≅ A
  ≅-sym (hoeq f g ε η) = hoeq g f η ε

  syntax ≅-sym p = p ≅⁻¹

  ≅-trans : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : Set ℓ'} {C : Set ℓ''} →
            A ≅ B → B ≅ C → A ≅ C
  ≅-trans {A = A} {C = C} (hoeq f g ε η) (hoeq f₁ g₁ ε₁ η₁) = hoeq
    (f₁ ∘′ f ) (g ∘′ g₁) ε₂ η₂
    where
      abstract 
        ε₂ : (x : C) → f₁ (f (g (g₁ x))) ≡ x
        ε₂ = λ x → ap f₁ (ε (g₁ x)) ◾ ε₁ x
        η₂ : (x : A) → g (g₁ (f₁ (f x))) ≡ x
        η₂ = λ x → ap g (η₁ (f x)) ◾ η x

  syntax ≅-trans p q = p ≅◾ q
```

```agda
module ≅-Reasoning where

  open ≅-lemmas

  infix 3 _≅∎
  infixr 2 _≅⟨_⟩_
  infix 1 begin≅_

  begin≅_ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} →
            A ≅ B → A ≅ B
  begin≅ p = p

  _≅⟨_⟩_ : ∀ {ℓ ℓ' ℓ''} (A : Set ℓ) {B : Set ℓ'} {C : Set ℓ''} →
          A ≅ B → B ≅ C → A ≅ C
  A ≅⟨ p ⟩ q = p ≅◾ q

  _≅∎ : ∀ {ℓ} (A : Set ℓ) → A ≅ A
  _≅∎ _ = refl≅
```
