---
title: "Unit type"
subtitle: "Martin-Löf Type Theory"
description: "A minimal Type Theory in Martin-Löf style: Unit type"
---


```agda
{-# OPTIONS --without-K --safe #-}

module mltt.unit where

open import level renaming (zero to lzero; suc to lsuc) public
```

We could define this as a data type as
```agda-ignore
data 𝟙 : Set where
  * : 𝟙
```

```agda
record 𝟙 : Set where
  constructor *
```

#### Induction and recursion principles

```agda
𝟙-induction : ∀ {ℓ} (P : 𝟙 → Set ℓ) → P * → (x : 𝟙) → P x
𝟙-induction P a * = a

𝟙-recursion : ∀ {ℓ} (B : Set ℓ) → B → 𝟙 → B
𝟙-recursion B = 𝟙-induction (λ _ → B)

-- direct version
𝟙-recursion' : ∀ {ℓ} (B : Set ℓ) → B → 𝟙 → B
𝟙-recursion' B b * = b

-- implicit version
𝟙-rec : ∀ {ℓ} {B : Set ℓ} → B → 𝟙 → B
𝟙-rec {ℓ} {B} = 𝟙-recursion {ℓ} B
```

#### Categorical property

There is a unique function from any type to 𝟙:

```agda
!𝟙 : ∀ {ℓ} {B : Set ℓ} → B → 𝟙
!𝟙 b = *
```

