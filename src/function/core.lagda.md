---
title: "Function: core"
subtitle: "Basic defintions on functions"
description: "Basic defintions on functions"
---

### Contents {#top}

1. [Functions](#functions)
1. [Convenience](#convenience)

--------------------------------------------------

```agda
{-# OPTIONS --without-K --safe #-}

module function.core where

open import level renaming (zero to lzero; suc to lsuc) public
```

### Functions {#functions}

Definitions copied from the standard library

```agda
-- identity
id : ∀ {ℓ} {A : Set ℓ} → A → A
id x = x

-- dependent composition
infixr 9 _∘_
_∘_ : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {E : A → Set ℓ'} {K : {x : A} → E x → Set ℓ''} →
      (∀ {x} (y : E x) → K y) → (g : (x : A) → E x) →
      ((x : A) → K (g x))
f ∘ g = λ x → f (g x)

-- non-dependent version (primed ′=\')
infixr 9 _∘′_
_∘′_ : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : Set ℓ'} {C : Set ℓ''} →
       (B → C) → (A → B) → (A → C)
f ∘′ g = f ∘ g
```

### Convenience {#convenience}

Trick to recover implicit arguments from functions without the need of giving them as arguments
```agda
domain : ∀{ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → (A → B) → Set ℓ
domain {ℓ} {ℓ'} {A} {B} f = A

codomain : ∀{ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → (A → B) → Set ℓ'
codomain {ℓ} {ℓ'} {A} {B} f = B
```
Evaluation maps are a standard thing
```agda
ev' : ∀ {ℓ ℓ'} {A : Set ℓ} {E : A → Set ℓ'} (x : A) → ((x : A) → E x) → E x
ev' x f = f x

ev : ∀ {ℓ ℓ'} {A : Set ℓ} {E : A → Set ℓ'} → ((x : A) → E x) → (x : A) → E x
ev f x = f x
```
This allows to recover the type of a term. 
```agda
---FIXME. This particular fragment needs to be moved in a general notation section
type-of : ∀{ℓ} {A : Set ℓ} → A → Set ℓ
type-of {ℓ} {A} x = A
```
