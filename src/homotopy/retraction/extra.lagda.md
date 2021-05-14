---
title: "Retraction: extra"
description: "Additional facts about retractions"
---

### Contents {#top}

1. [Sigma types](#sigma)

--------------------------------------------------

```agda
{-# OPTIONS --without-K --safe #-}

module homotopy.retraction.extra where

open import level
open import mltt
open import function
open import homotopy.naturality
open import homotopy.fibrations
open import homotopy.retraction.core

open ≡-Reasoning
open transport-lemmas
open ◾-lemmas
```

### Sigma types {#sigma}

Pointwise retractions of dependent types give retractions of the total spaces

```agda
Σ-retract : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {P : A → Set ℓ'} {Q : A → Set ℓ''} →
            ((x : A) → (P x) ◅ (Q x)) → (Σ A P) ◅ (Σ A Q)
Σ-retract {A = A} {P} {Q} ρ = record { retr = Nat→Σ r ; sect = Nat→Σ s ; homot = η }
  where
    r : (x : A) → Q x → P x
    r x = retract (ρ x)
    s : (x : A) → P x → Q x
    s x = section (ρ x)
    h : (x : A) (u : P x) → r x (s x u) ≡ u
    h x = retract-homotopy (ρ x)
    η : Nat→Σ r ∘′ Nat→Σ s ~ id
    η (x , u) = begin
                x , r x (s x u) ≡⟨ ap (λ v → x , v) (h x u) ⟩
                x , u ∎
```


If `P : A → Set ν` and `r : B → A` has a section, so that in effect
`A` is a retraction of `B`, then the total space `Σ[ a ∈ A ] P a` is a
retraction of the pull-back `Σ[ b ∈ B ] P (f b)`.

```agda
Σ-pullback-retract : ∀ {ℓ ℓ' ν} {A : Set ℓ} {B : Set ℓ'} {P : A → Set ν} (r : B → A) → 
                     has-sect r → ( Σ[ a ∈ A ] P a ) ◅ ( Σ[ b ∈ B ] P (r b) )
Σ-pullback-retract {A = A} {B = B} {P = P} r (s , η) = record { retr = ρ
                                                              ; sect = σ
                                                              ; homot = Η }
  where
    ρ : Σ[ b ∈ B ] P (r b) → Σ[ a ∈ A ] P a 
    ρ (b , v) = (r b) , v

    σ : Σ[ a ∈ A ] P a → Σ[ b ∈ B ] P (r b)
    σ (a , u) = (s a) , transport P ((η a) ⁻¹) u

    -- Greek upper-case Eta
    Η : (y : Σ[ a ∈ A ] P a) → ρ (σ y) ≡ y 
    Η (a , u) = PathPair→PathΣ (pp (a , u))
      where
        open transport-lemmas
        pp : (y : Σ[ a ∈ A ] P a) → ρ (σ y) ╝ y
        π₁ (pp (a , u)) = η a
        π₂ (pp (a , u)) = transport P (η a) (transport P (η a ⁻¹) u) ≡⟨ transport◾ (η a ⁻¹) (η a) ⟩
                             transport P ((η a ⁻¹) ◾ (η a)) u ≡⟨ transport≡ (linv (η a)) ⟩
                             u ∎

```

