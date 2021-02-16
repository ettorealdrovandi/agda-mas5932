---
title: "Natural Numbers"
subtitle: "Standard and simple types in Martin-Löf Type Theory"
description: "Core: definitions, and operations"
---

### Contents {#top}

1. [Main](#main)
1. [Induction and recursion](#indrec)
1. [Operations](#ops)

--------------------------------------------------

```agda
{-# OPTIONS --without-K --safe #-}

module types.naturals.core where

open import level renaming (zero to lzero; suc to lsuc)
```


### Main {#main}

```agda
data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}


pred : ℕ → ℕ
pred zero = zero
pred (suc n) = n
```

### Induction and recursion {#indrec}

```agda
ℕ-induction : ∀ {ℓ} {A : ℕ → Set ℓ} → A 0 → ( (n : ℕ) → A n → A (suc n)) → (n : ℕ) → A n
ℕ-induction a₀ f zero = a₀
ℕ-induction a₀ f (suc n) = f n (ℕ-induction a₀ f n)

ℕ-recursion : ∀ {ℓ} {A : Set ℓ} → A → (ℕ → A → A) → ℕ → A
ℕ-recursion {ℓ} {A} = ℕ-induction {A = λ _ → A } 

ℕ-iteration : ∀ {ℓ} {A : Set ℓ} → A → (A → A) → ℕ → A
ℕ-iteration a f = ℕ-recursion a (λ _ → f ) 
```

### Operations {#ops}

```agda
infix 20 _+_
infix 21 _*_
infix 22 _^_
  
_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

_*_ : ℕ → ℕ → ℕ
zero * n = zero
suc m * n = m * n + n

_^_ : ℕ → ℕ → ℕ
m ^ zero = 1
m ^ suc n = m * m ^ n
```

The operations can be defined using the iteration structure
```agda
private
  module ℕ-ops' where

    infix 20 _+'_
    infix 21 _*'_

    _+'_ : ℕ → ℕ → ℕ
    m +' n = h m where
          h : ℕ → ℕ 
          h = ℕ-iteration n suc

    _*'_ : ℕ → ℕ → ℕ
    m *' n = h m where
       h : ℕ → ℕ
       h = ℕ-iteration 0 (_+' n)

    _^'_ : ℕ → ℕ → ℕ
    m ^' n = h m
      where
        h : ℕ → ℕ
        h = ℕ-iteration 1 (_*' n)
```
