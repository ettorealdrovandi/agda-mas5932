---
title: "Natural Numbers"
subtitle: "Standard and simple types in Martin-Löf Type Theory"
description: "Order: elementary lemmas or order
---

### Contents {#top}


--------------------------------------------------

```agda
{-# OPTIONS --without-K --safe --exact-split #-}

module types.naturals.order where

open import level
open import mltt.identity.core
open import mltt.empty
open import mltt.unit
open import types.naturals.core
```

```agda
data _≦_ : ℕ → ℕ → Set where
  z≦n : ∀ {n} → 0 ≦ n
  s≦s : ∀ {m n} (p : m ≦ n) → suc m ≦ suc n

≦-lc-suc : ∀ {m n} → suc m ≦ suc n → m ≦ n
≦-lc-suc (s≦s x) = x

≦-refl : ∀ {n} → n ≦ n
≦-refl {zero} = z≦n
≦-refl {suc n} = s≦s ≦-refl

≡→≦ : ∀ {m n} → m ≡ n → m ≦ n
≡→≦ {m} {.m} refl = ≦-refl

≦-trans : ∀ {m n p} → m ≦ n → n ≦ p → m ≦ p
≦-trans z≦n _ = z≦n
≦-trans (s≦s u) (s≦s v) = s≦s (≦-trans u v)

≦-antisym : ∀ {m n} → m ≦ n → n ≦ m → m ≡ n
≦-antisym z≦n z≦n = refl
≦-antisym (s≦s p) (s≦s q) = ap suc (≦-antisym p q)

≦-suc : ∀ {n} → n ≦ suc n
≦-suc {zero} = z≦n
≦-suc {suc n} = s≦s ≦-suc

≦̸-suc : ∀ {n} → ¬ (suc n ≦ n)
≦̸-suc {suc n} x =  ≦̸-suc (≦-lc-suc x) 

-- this is just the constructor
zero-≦-inf : ∀ {n} → 0 ≦ n
zero-≦-inf = z≦n

unique-≦-inf : ∀ {n} → n ≦ 0 → n ≡ 0
unique-≦-inf {zero} p = refl
```

```agda
infix 10 _≤_
infix 10 _≥_

_≤_ : ℕ → ℕ → Set
zero ≤ n = 𝟙
suc m ≤ zero = 𝟘
suc m ≤ suc n = m ≤ n

_≥_ : ℕ → ℕ → Set
m ≥ n = m ≤ n
```

```agda
≤→≦ : ∀ {m n} → m ≤ n → m ≦ n
≤→≦ {zero} {n} _ = z≦n
≤→≦ {suc m} {suc n} p = s≦s (≤→≦ p)

≦→≤ : ∀ {m n} → m ≦ n → m ≤ n
≦→≤ {zero} {n} _ = *
≦→≤ {suc m} {suc n} x = ≦→≤ {m} {n} (≦-lc-suc x)
```

<p style="font-size: smaller; text-align: right">[top ⇑](#top)</p>
---
