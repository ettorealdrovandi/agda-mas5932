---
title: "Natural Numbers"
subtitle: "Standard and simple types in Martin-Löf Type Theory"
description: "Order: comparison between the two definitions of leq
---


```agda
{-# OPTIONS --without-K --safe --exact-split #-}

module types.naturals.order.comparison where


open import mltt.unit
open import types.naturals.core
open import types.naturals.order.core renaming (_≤_ to _≦_;
                                               z≤n to z≦n;
                                               s≤s to s≦s;
                                               ≤-lc-suc to ≦-lc-suc)
open import types.naturals.order.alternative
```

```agda
≤→≦ : ∀ {m n} → m ≤ n → m ≦ n
≤→≦ {zero} {n} _ = z≦n
≤→≦ {suc m} {suc n} p = s≦s (≤→≦ p)

≦→≤ : ∀ {m n} → m ≦ n → m ≤ n
≦→≤ {zero} {n} _ = *
≦→≤ {suc m} {suc n} x = ≦→≤ {m} {n} (≦-lc-suc x)
```
