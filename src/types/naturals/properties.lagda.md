---
title: "Natural Numbers"
subtitle: "Standard and simple types in Martin-Löf Type Theory"
description: "Properties: elementary theorems"
---

### Contents {#top}


--------------------------------------------------

```agda
{-# OPTIONS --without-K --safe #-}

module types.naturals.properties where

open import level renaming (zero to lzero; suc to lsuc)
open import function
open import mltt.identity.core 
open import types.naturals.core

open ≡-Reasoning
```

The following *inductive hypothesis* is used in several places and it
can be used to show that + can be defined by recursion on the right
variable. (The proof uses `+-right-unit` as the base case.)

```agda
private 
  ih : ∀ m y → suc (m + y) ≡ m + suc y
  ih zero y = idp (suc y)
  ih (suc m) y = ap suc (ih m y)
```

---

```agda
+-left-unit : ∀ n → 0 + n ≡ n
+-left-unit n = refl

+-right-unit : ∀ n → n + 0 ≡ n
+-right-unit zero = refl
+-right-unit (suc n) = ap suc (+-right-unit n)

+-assoc : ∀ m n p → (m + n) + p ≡ m + (n + p)
+-assoc zero n p = refl
+-assoc (suc m) n p = suc ((m + n) + p) ≡⟨ ap suc (+-assoc m n p) ⟩
                      suc (m + (n + p)) ∎

+-left-cancel : ∀ n → left-cancelable (n +_)
+-left-cancel zero = λ z → z
+-left-cancel (suc n) p = +-left-cancel n (ap pred p)

+-right-cancel : ∀ n → left-cancelable (_+ n)
+-right-cancel zero {x} {y} p = x     ≡⟨ (+-right-unit x) ⁻¹ ⟩
                                x + 0 ≡⟨ p ⟩
                                y + 0 ≡⟨ +-right-unit y ⟩                                
                                y ∎
+-right-cancel (suc n) {x} {y} p = +-right-cancel n (suc-inj q)
  where
    q : suc (x + n) ≡ suc (y + n)
    q = suc (x + n) ≡⟨ ih x n ⟩
        x + suc n   ≡⟨ p ⟩
        y + suc n   ≡⟨ (ih y n) ⁻¹ ⟩
        suc (y + n) ∎

+-comm : ∀ m n → m + n ≡ n + m
+-comm zero n = (+-right-unit n) ⁻¹
+-comm (suc m) n = suc (m + n) ≡⟨ ap suc (+-comm m n) ⟩
                   suc (n + m) ≡⟨ ih n m ⟩
                   n + suc m ∎

right-distr : ∀ m n p → (m + n) * p ≡ m * p + n * p
right-distr zero n p = idp (n * p)
right-distr (suc m) n p = (m + n) * p + p     ≡⟨ ap (_+ p) (right-distr m n p) ⟩
                          (m * p + n * p) + p ≡⟨ +-assoc (m * p) (n * p) p ⟩
                          m * p + (n * p + p) ≡⟨ ap (_+_ (m * p)) (+-comm (n * p) p) ⟩
                          m * p + (p + n * p) ≡⟨ (+-assoc (m * p) p (n * p)) ⁻¹ ⟩
                          (m * p + p) + n * p ∎


left-distr : ∀ m n p → m * (n + p) ≡ m * n + m * p
left-distr zero n p = refl
left-distr (suc m) n p = begin
  m * (n + p) + (n + p)     ≡⟨ ap (_+ (n + p)) (left-distr m n p) ⟩
  (m * n + m * p) + (n + p) ≡⟨ +-assoc (m * n) (m * p) (n + p) ⟩
  m * n + (m * p + (n + p)) ≡⟨ ap ((m * n) +_ ) (+-assoc (m * p) n p) ⁻¹ ⟩
  m * n + ((m * p + n) + p) ≡⟨ ap (m * n +_) (ap (_+ p) (+-comm (m * p) n)) ⟩
  m * n + ((n + m * p) + p) ≡⟨ ap (m * n +_) (+-assoc n (m * p) p) ⟩
  m * n + (n + (m * p + p)) ≡⟨ (+-assoc (m * n) n (m * p + p)) ⁻¹ ⟩
  (m * n + n) + (m * p + p)
  ∎

*-left-unit : ∀ n → 1 * n ≡ n
*-left-unit n = idp  n

*-right-unit : ∀ n → n * 1 ≡ n
*-right-unit zero = idp 0
*-right-unit (suc n) = begin
  n * 1 + 1       ≡⟨ (ih (n * 1) 0) ⁻¹ ⟩
  suc (n * 1 + 0) ≡⟨ ap suc (+-right-unit (n * 1)) ⟩
  suc (n * 1)     ≡⟨ ap suc (*-right-unit n) ⟩
  suc n
  ∎

*-assoc : ∀ m n p → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p = begin 
  (m * n + n) * p     ≡⟨ right-distr (m * n) n p ⟩
  (m * n) * p + n * p ≡⟨ ap (_+ (n * p)) (*-assoc m n p) ⟩
  m * (n * p) + n * p
  ∎

left-zero : ∀ n → 0 * n ≡ 0
left-zero n = refl

right-zero : ∀ n → n * 0 ≡ 0
right-zero zero = refl
right-zero (suc n) = ap (_+ 0) (right-zero n)

*-comm : ∀ m n → m * n ≡ n * m
*-comm zero n = (right-zero n) ⁻¹ 
*-comm (suc m) n = begin
  m * n + n      ≡⟨ +-comm (m * n) n ⟩
  n + m * n      ≡⟨ ap (n +_) (*-comm m n) ⟩
  n + n * m      ≡⟨ ap (_+ (n * m)) (*-right-unit n) ⁻¹ ⟩
  n * 1  + n * m ≡⟨ (left-distr n 1 m) ⁻¹ ⟩
  n * (1 + m)    ≡⟨ refl ⟩
  n * suc m
  ∎
```
