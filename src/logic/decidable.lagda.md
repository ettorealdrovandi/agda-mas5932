---
title: "Decidable"
description: "Definition of decidable type"
---

```agda
{-# OPTIONS --without-K --safe #-}

module logic.decidable where

open import level
open import mltt.sum
open import mltt.empty
open import mltt.identity.core
```

```agda
decidable : ∀ {ℓ} → Set ℓ → Set ℓ
decidable A = A + ¬ A

decidable-equality : ∀ {ℓ} → Set ℓ → Set ℓ
decidable-equality A = (x y : A) → decidable (x ≡ y)
```

