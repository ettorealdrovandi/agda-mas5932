---
title: "Sum types"
subtitle: "Martin-Löf Type Theory"
description: "A minimal Type Theory in Martin-Löf style: sum types, aka disjoint unions"
---


```agda
{-# OPTIONS --without-K --safe #-}

module mltt.sum where

open import level
```

```agda
-- Can't use ⊔ since it is taken by universe upper bound
data _⊎_ {ℓ ℓ' : Level} (A : Set ℓ) (B : Set ℓ') : Set (ℓ ⊔ ℓ') where
  inl : A → A ⊎ B
  inr : B → A ⊎ B
```

#### Induction and recursion

```agda
⊎-induction : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : Set ℓ'} (P : A ⊎ B → Set ℓ'') →
             ((a : A) → P (inl a)) →
             ((b : B) → P (inr b)) →
             (ab : A ⊎ B) → P ab
⊎-induction P f g (inl a) = f a
⊎-induction P f g (inr b) = g b

⊎-recursion : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : Set ℓ'} {C : Set ℓ''} →
           (A → C) → (B → C) → A ⊎ B → C
⊎-recursion {C = C} = ⊎-induction (λ _ → C)
```

Of course, we also have a direct definition of recursion

```agda
⊎-recursion' : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : Set ℓ'} {C : Set ℓ''} →
            (A → C) → (B → C) → A ⊎ B → C
⊎-recursion' f g (inl a) = f a
⊎-recursion' f g (inr b) = g b
```

