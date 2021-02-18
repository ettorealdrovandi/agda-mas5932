---
title: "The type with two elements"
subtitle: "Standard and simple types in Martin-Löf Type Theory"
description: "Disjoint union (sum) of two unit types: the type with two canonical terms"
---


```agda
{-# OPTIONS --without-K --safe #-}

module types.two where

open import level
open import mltt.unit
open import mltt.sum
```

```agda
𝟚 : Set
𝟚 = 𝟙 + 𝟙
-----
pattern ₀ = inl *
pattern ₁ = inr *
```

#### Induction and recursion principles

```agda
-- induction and recursion: direct definition
𝟚-induction : ∀ {ℓ} (P : 𝟚 → Set ℓ) → P ₀ → P ₁ → (i : 𝟚) → P i
𝟚-induction P p₀ p₁ ₀ = p₀
𝟚-induction P p₀ p₁ ₁ = p₁


𝟚-induction' : ∀ {ℓ} (P : 𝟚 → Set ℓ) → P ₀ → P ₁ → (i : 𝟚) → P i
𝟚-induction' P p₀ p₁ = +induction P 
                           (𝟙-induction (λ x → P (inl x)) p₀) 
                           (𝟙-induction (λ x → P (inr x)) p₁) 


-- recursion
𝟚-recursion : ∀ {ℓ} (P : Set ℓ) → P → P → 𝟚 → P
𝟚-recursion P = 𝟚-induction (λ _ → P)
```

#### Types dependent on 𝟚

```agda
𝟚-to-dep' : ∀ {ℓ} (A B : Set ℓ) → 𝟚 → Set ℓ
𝟚-to-dep' A B ₀ = A
𝟚-to-dep' A B ₁ = B

𝟚-to-dep : ∀ {ℓ} (A B : Set ℓ) → 𝟚 → Set ℓ
𝟚-to-dep {ℓ} A B = 𝟚-recursion (Set ℓ) A B
infix 40 _⋆_
_⋆_ = 𝟚-to-dep
```
