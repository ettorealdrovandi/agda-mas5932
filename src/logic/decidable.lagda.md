---
title: "Decidable"
description: "Definition of decidable type"
---

```agda
{-# OPTIONS --without-K --safe --exact-split #-}

module logic.decidable where

open import level
open import mltt.empty
open import mltt.unit
open import mltt.sum
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

```agda
open import logic.negation
open import function.id-to-fun
open import types.two

one-is-not-zero : 𝟙 ≢ 𝟘
one-is-not-zero = λ p → Id→Fun p *

₁-is-not-₀ : ₁ ≢ ₀
₁-is-not-₀ p = one-is-not-zero q
  where
    q : 𝟙 ≡ 𝟘
    q = ap (𝟚-to-dep 𝟘 𝟙) p

inl-is-not-inr : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'}
                          {a : A} {b : B} →
                          inl a ≢ inr b
inl-is-not-inr {ℓ} {ℓ'} {A} {B} {a} {b} p = one-is-not-zero q
  where
    f : A + B → Set
    f = +recursion (λ _ → 𝟙) (λ _ → 𝟘)

    q : 𝟙 ≡ 𝟘
    q = ap f p

inl-is-not-inr' : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'}
                           {a : A} {b : B} →
                           inl a ≢ inr b
inl-is-not-inr' = λ ()

₁-is-not-₀' : ₁ ≢ ₀
₁-is-not-₀' = ≢-inv (inl-is-not-inr {A = 𝟙} {B = 𝟙} {*} {*})
```

```agda
𝟚-decidable-equality : decidable-equality 𝟚
𝟚-decidable-equality ₀ ₀ = inl (idp ₀)
𝟚-decidable-equality ₀ ₁ = inr (≢-inv ₁-is-not-₀)
𝟚-decidable-equality ₁ ₀ = inr (₁-is-not-₀)
𝟚-decidable-equality ₁ ₁ = inl (idp ₁)
```
