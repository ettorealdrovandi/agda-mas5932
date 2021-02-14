---
title: "Natural Numbers"
subtitle: "Standard and simple types in Martin-Löf Type Theory"
description: "Core: definitions, and operations"
---

### Contents {#top}

1. [Induction and recursion](#indrec)

--------------------------------------------------

```agda
{-# OPTIONS --without-K --safe #-}

module types.naturals.core where

open import level renaming (zero to lzero; suc to lsuc)


data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}
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
infix 20 _+ℕ_
infix 21 _*ℕ_
infix 22 _^ℕ_
  
_+ℕ_ : ℕ → ℕ → ℕ
zero +ℕ n = n
suc m +ℕ n = suc (m +ℕ n)

_*ℕ_ : ℕ → ℕ → ℕ
zero *ℕ n = zero
suc m *ℕ n = m *ℕ n +ℕ n

_^ℕ_ : ℕ → ℕ → ℕ
m ^ℕ zero = 1
m ^ℕ suc n = m *ℕ m ^ℕ n
```

The operations can be defined using the iteration structure
```agda
private
  module ℕ-ops' where

    infix 20 _+'ℕ_
    infix 21 _*'ℕ_

    _+'ℕ_ : ℕ → ℕ → ℕ
    m +'ℕ n = h m where
          h : ℕ → ℕ 
          h = ℕ-iteration n suc

    _*'ℕ_ : ℕ → ℕ → ℕ
    m *'ℕ n = h m where
       h : ℕ → ℕ
       h = ℕ-iteration 0 (_+ℕ n)

    _^'ℕ_ : ℕ → ℕ → ℕ
    m ^'ℕ n = h m
      where
        h : ℕ → ℕ
        h = ℕ-iteration 1 (_*ℕ n)
```
