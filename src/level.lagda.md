---
title: "Universe levels and lifts"
description: "Universe levels and lifts"
copyright: "Copyright © 2020-2021 Ettore Aldrovandi"
---

```agda
------------------------------------------------------------------------
-- Copied from the Agda standard library
-- So we do not have to depend on it
--
-- Universe levels
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module level where

-- Levels.

open import Agda.Primitive as Prim public
  using    (Level; _⊔_; Setω; lzero; lsuc)

-- Lifting.

record Lift {a} ℓ (A : Set a) : Set (a ⊔ ℓ) where
  constructor lift
  field lower : A

open Lift public

-- Synonyms

0ℓ : Level
0ℓ = lzero

1ℓ : Level
1ℓ = lsuc 0ℓ

levelOfType : ∀ {a} → Set a → Level
levelOfType {a} _ = a

levelOfTerm : ∀ {a} {A : Set a} → A → Level
levelOfTerm {a} _ = a
```
