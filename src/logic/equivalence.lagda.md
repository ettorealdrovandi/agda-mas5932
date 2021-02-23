---
title: "Equivalence"
description: "Definition of logical equivalence"
---

```agda
{-# OPTIONS --without-K --safe #-}

module logic.equivalence where

open import level
open import mltt.sigma
```

Definition of logical equivalence  
**FIXME:** for want of a better place
```agda
_⟺_ : ∀ {ℓ ℓ'} → Set ℓ →  Set ℓ' → Set (ℓ ⊔ ℓ')
A ⟺ B = (A → B) × (B → A)
```
