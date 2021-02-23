---
title: "Negation"
description: "Definitions using ¬ and ≢"
---

```agda
{-# OPTIONS --without-K --safe #-}

module logic.negation where

open import level
open import mltt.empty
open import mltt.identity.core
```

Double an triple negation, for convenience
```agda
¬¬ ¬¬¬ : ∀ {ℓ} (A : Set ℓ) → Set ℓ
¬¬ A  = ¬ (¬ A)
¬¬¬ A = ¬ (¬¬ A)
```

If we have a term `a : A`, then `A` is not empty, i.e. we get a term of `¬¬ A`:
```agda
¬¬-intro : ∀ {ℓ} {A : Set ℓ} → A → (¬¬ A)
¬¬-intro a = λ x → x a
```

Standard contrapositive: if `a : B`, then `f a : B`, so `¬b (f a) : 𝟘` i.e. we get `¬ A`:
```agda
contra : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → (A → B) → (¬ B → ¬ A)
contra f = λ ¬b a → ¬b (f a)
```

Three negations imply one and its converse:
```agda
three-to-one¬ : ∀ {ℓ} {A : Set ℓ} → ¬¬¬ A → ¬ A
three-to-one¬ = contra ( ¬¬-intro )

one-to-three¬ : ∀ {ℓ} {A : Set ℓ} → ¬ A → ¬¬¬ A
one-to-three¬ = λ x → ¬¬-intro x
```

Negation of equality
```agda
_≢_ : ∀ {ℓ} {A : Set ℓ} → A → A → Set ℓ
x ≢ y = ¬ (x ≡ y)

≢-inv : ∀ {ℓ} {A : Set ℓ} {x y : A} → x ≢ y → y ≢ x
≢-inv u = λ p → u (p ⁻¹)
```
