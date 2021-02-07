---
title: "Empty type"
subtitle: "Martin-Löf Type Theory"
description: "A minimal Type Theory in Martin-Löf style: Empty type"
---

```agda
{-# OPTIONS --without-K --safe #-}

module mltt.empty where

open import level renaming (zero to lzero; suc to lsuc) public

data 𝟘 : Set where  --complete definition, no constructor
```

Induction and recursion principles for 𝟘:

```agda
𝟘-induction : ∀ {ℓ} (P : 𝟘 → Set ℓ) → (x : 𝟘) → P x
𝟘-induction P ()

𝟘-recursion : ∀ {ℓ} (B : Set ℓ) → 𝟘 → B
𝟘-recursion B = 𝟘-induction (λ _ → B) 

-- Direct definition
𝟘-recursion' : ∀ {ℓ} (B : Set ℓ) → 𝟘 → B
𝟘-recursion' B ()

-- Same but B implicit
𝟘-recursion'' : ∀ {ℓ} {B : Set ℓ} → 𝟘 → B
𝟘-recursion'' ()
```

There is a unique function from 𝟘 to any type

```agda
!𝟘 : ∀ {ℓ} {B : Set ℓ} → 𝟘 → B
!𝟘 = 𝟘-recursion''
```

The empty type can be used as a predicate to express emptiness…
```agda
is-empty : ∀ {ℓ} → Set ℓ → Set ℓ
is-empty B = B → 𝟘
```
…or falsity:
    
```agda
-- logically
¬ : ∀ {ℓ} → Set ℓ → Set ℓ
¬ B = B → 𝟘
```
