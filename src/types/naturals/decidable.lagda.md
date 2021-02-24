---
title: "Natural Numbers"
subtitle: "Standard and simple types in Martin-Löf Type Theory"
description: "The type ℕ has decidable equality "
---

### Contents {#top}


--------------------------------------------------

```agda
{-# OPTIONS --without-K --safe #-}

module types.naturals.decidable where

open import level
open import mltt.sum
open import logic
open import mltt.identity.core 
open import types.naturals.core
open import types.naturals.order
```

```agda
zero-not-suc : (n : ℕ) → suc n ≢ 0
zero-not-suc n p = ≰-suc q
  where
    q : suc n ≤ n
    q = ≤-trans (≡→≤ p) zero-≤-inf

ℕ-decidable-equality : decidable-equality ℕ
ℕ-decidable-equality zero zero = inl (idp 0)
ℕ-decidable-equality zero (suc n) = inr (≢-inv (zero-not-suc n))
ℕ-decidable-equality (suc m) zero = inr (zero-not-suc m)
ℕ-decidable-equality (suc m) (suc n) = f (ℕ-decidable-equality m n)
  where
    f : decidable (m ≡ n) → decidable (suc m ≡ suc n)
    f (inl p) = inl (ap suc p)
    f (inr q) = inr (λ x → q (suc-inj x))
```
