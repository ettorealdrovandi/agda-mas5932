---
title: "Universe"
description: "Alternative universe name"
---

```agda
{-# OPTIONS --without-K --safe #-}

module mltt.universe where

open import level public

𝕌 : (ℓ : Level) → Set (lsuc ℓ)
𝕌 = λ ℓ → Set ℓ

𝕌₀ = 𝕌 0ℓ
𝕌₁ = 𝕌 (lsuc 0ℓ)
```
