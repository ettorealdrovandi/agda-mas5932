---
title: "Natural Numbers"
subtitle: "Standard and simple types in Martin-Löf Type Theory"
description: "Order: alternative definitions and elementary lemmas or order
---

### Contents {#top}

1. [≤,<](#leq)
1. [≥](#geq)

--------------------------------------------------

```agda
{-# OPTIONS --without-K --safe --exact-split #-}

module types.naturals.order.alternative where

open import level
open import mltt.identity.core
open import mltt.empty
open import mltt.sum renaming (_+_ to _⊎_)
open import mltt.unit
open import types.naturals.core
```

### `≤, <`  {#leq}

```agda

infix 10 _≤_
infix 10 _≥_

_≤_ : ℕ → ℕ → Set
zero ≤ n = 𝟙
suc m ≤ zero = 𝟘
suc m ≤ suc n = m ≤ n

_≥_ : ℕ → ℕ → Set
m ≥ n = m ≤ n

≤-lc-suc : ∀ {m n} → suc m ≤ suc n → m ≤ n
≤-lc-suc p = p

≤-refl : ∀ {n} → n ≤ n
≤-refl {zero} = *
≤-refl {suc n} = ≤-refl {n}

≡→≤ : ∀ {m n} → m ≡ n → m ≤ n
≡→≤ {m} {.m} refl = ≤-refl {m}

≤-trans : ∀ {l m n} → l ≤ m → m ≤ n → l ≤ n
≤-trans {zero} {m} {n} _ _ = *
≤-trans {suc l} {suc m} {suc n} p q = ≤-trans {l} {m} {n} p q

≤-antisym : ∀ {m n} → m ≤ n → n ≤ m → m ≡ n
≤-antisym {zero} {zero} p q = refl
≤-antisym {suc m} {suc n} p q = ap suc (≤-antisym p q)

≤-suc : ∀ {n} → n ≤ suc n
≤-suc {zero} = *
≤-suc {suc n} = ≤-suc {n}

≰-suc : ∀ {n} → ¬ (suc n ≤ n)
≰-suc {zero} = λ z → z
≰-suc {suc n} = λ x → ≰-suc {n} x

zero-≤-inf : ∀ {n} → 0 ≤ n
zero-≤-inf = *

unique-≤-inf : ∀ {n} → n ≤ 0 → n ≡ 0
unique-≤-inf {zero} = λ x → refl
unique-≤-inf {suc n} = λ () -- found automatically

≤-less-than-suc : ∀ {m n} → m ≤ n → m ≤ suc n
≤-less-than-suc {m} {n} p = ≤-trans {m} p (≤-suc {n})

≤-split : ∀ {m n} → m ≤ suc n → (m ≤ n) ⊎ (m ≡ suc n)
≤-split {zero} {n} p = inl *
≤-split {suc m} {zero} p = inr (ap suc (unique-≤-inf {m} p))
≤-split {suc m} {suc n} p = +recursion inl (λ x → inr (ap suc x)) 
                                       (≤-split {m} {n} p)
```

### ≥ {#geq}

```agda

_<_ : ℕ → ℕ → Set
m < n = suc m ≤ n
infix 10 _<_


z<n : ∀ {n} → 0 < suc n
z<n = *

<→≤ : ∀ {m n} → m < n → m ≤ n
<→≤ {m} {n} p = ≤-trans {m} {suc m} {n} (≤-suc {m}) p

<-trans : ∀ {m n p} → m < n → n < p → m < p
<-trans {m} {n} {p} u v = ≤-trans {suc m} {n} {p} u (<→≤ {n} v)

<-ap-suc : ∀ {m n} → m < n → suc m < suc n
<-ap-suc = λ z → z
```


<p style="font-size: smaller; text-align: right">[top ⇑](#top)</p>
---
