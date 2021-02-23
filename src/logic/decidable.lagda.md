---
title: "Decidable"
description: "Definition of decidable type"
---

```agda
{-# OPTIONS --without-K --safe --exact-split #-}

module logic.decidable where

open import level
open import mltt.sum
open import mltt.empty
open import mltt.unit
open import mltt.identity.core
```

```agda
decidable : ∀ {ℓ} → Set ℓ → Set ℓ
decidable A = A + ¬ A

decidable-equality : ∀ {ℓ} → Set ℓ → Set ℓ
decidable-equality A = (x y : A) → decidable (x ≡ y)
```

```agda
true : ∀ {ℓ} {A : Set ℓ} → decidable A → Set
true (inl x) = 𝟙
true (inr x) = 𝟘

witness : ∀ {ℓ} {A : Set ℓ} {d : decidable A} → true d → A
witness {ℓ} {A} {inl x} _ = x
witness {ℓ} {A} {inr x} t = !𝟘 {B = A} t -- Agda does not need this

decide : ∀ {ℓ} {A : Set ℓ} {d : decidable A} → A → true d
decide {ℓ} {A} {inl x} = λ _ → *
decide {ℓ} {A} {inr x} = x
```

