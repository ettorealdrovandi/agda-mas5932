---
title: "Natural Numbers"
subtitle: "Standard and simple types in Martin-Löf Type Theory"
description: "Order: definitions and elementary lemmas or order
---

### Contents {#top}

1. [≤](#leq)
1. [<](#lt)
1. [≥](#geq)

--------------------------------------------------

```agda
{-# OPTIONS --without-K --safe --exact-split #-}

module types.naturals.order.core where

open import level
open import mltt.identity.core
open import mltt.empty
open import mltt.sum renaming (_+_ to _⊎_)
open import types.naturals.core
```

### ≤ {#leq}

```agda
data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n} → 0 ≤ n
  s≤s : ∀ {m n} (p : m ≤ n) → suc m ≤ suc n

≤-lc-suc : ∀ {m n} → suc m ≤ suc n → m ≤ n
≤-lc-suc (s≤s x) = x

≤-refl : ∀ {n} → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl

≡→≤ : ∀ {m n} → m ≡ n → m ≤ n
≡→≤ {m} {.m} refl = ≤-refl

≤-trans : ∀ {m n p} → m ≤ n → n ≤ p → m ≤ p
≤-trans z≤n _ = z≤n
≤-trans (s≤s u) (s≤s v) = s≤s (≤-trans u v)

≤-antisym : ∀ {m n} → m ≤ n → n ≤ m → m ≡ n
≤-antisym z≤n z≤n = refl
≤-antisym (s≤s p) (s≤s q) = ap suc (≤-antisym p q)

≤-suc : ∀ {n} → n ≤ suc n
≤-suc {zero} = z≤n
≤-suc {suc n} = s≤s ≤-suc

≰-suc : ∀ {n} → ¬ (suc n ≤ n)
≰-suc {suc n} x =  ≰-suc (≤-lc-suc x) 

-- this is just the constructor
zero-≤-inf : ∀ {n} → 0 ≤ n
zero-≤-inf = z≤n

unique-≤-inf : ∀ {n} → n ≤ 0 → n ≡ 0
unique-≤-inf {zero} p = refl

≤-less-than-suc : ∀ {m n} → m ≤ n → m ≤ (suc n)
≤-less-than-suc p = ≤-trans p ≤-suc

≤-split : ∀ {m n} → m ≤ suc n → (m ≤ n) ⊎ (m ≡ suc n)
≤-split {zero} {n} p = inl z≤n
≤-split {suc m} {zero} p = inr (ap suc (unique-≤-inf (≤-lc-suc p))) 
≤-split {suc m} {suc n} p = +recursion (λ z → inl (s≤s z)) 
                                       (λ x → inr (ap suc x)) 
                                       ((≤-split (≤-lc-suc p)))
```

### < {#lt}

```agda
infix 10 _≤_
infix 10 _≥_

_≥_ : ℕ → ℕ → Set
m ≥ n = n ≤ m
```

### ≥ {#geq}

```agda
_<_ : ℕ → ℕ → Set
m < n = suc m ≤ n
infix 10 _<_

z<n : ∀ {n} → 0 < suc n
z<n = s≤s z≤n

<→≤ : ∀ {m n} → m < n → m ≤ n
<→≤ {m} {n} p = ≤-trans (≤-suc {m}) p

<-trans : ∀ {m n p} → m < n → n < p → m < p
<-trans u v = <→≤ (≤-trans (s≤s u) v)

<-ap-suc : ∀ {m n} → m < n → suc m < suc n
<-ap-suc = s≤s
```


<p style="font-size: smaller; text-align: right">[top ⇑](#top)</p>
---

