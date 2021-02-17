---
title: "Function: general-notation"
subtitle: "Miscellaneous definitions and utilities"
description: "Miscellaneous definitions and utilities"
---

```agda
{-# OPTIONS --without-K --safe #-}

module function.general-notation where

open import level renaming (zero to lzero; suc to lsuc) 
open import function.core
open import mltt.identity.core
```

Naive injectivity
```agda
left-cancellable : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → (A → B) → Set (ℓ ⊔ ℓ')
left-cancellable f = {x y : domain f} → f x ≡ f y → x ≡ y

-- British v. American
left-cancelable = left-cancellable
```

