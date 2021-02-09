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
private
  variable
    ℓ ℓ' ℓ'' : Level
    A : Set ℓ
    B : Set ℓ'
    C : Set ℓ''

id : A → A
id x = x

-- dependent composition
infixr 9 _∘_
_∘_ : ∀ {A : Set ℓ} {B : A → Set ℓ'} {C : {x : A} → B x → Set ℓ''} →
      (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) →
      ((x : A) → C (g x))
f ∘ g = λ x → f (g x)

-- non-dependent version (primed ′=\')
infixr 9 _∘′_
_∘′_ : (B → C) → (A → B) → (A → C)
f ∘′ g = f ∘ g
```

### Convenience {#convenience}

```agda
module convenience where
```
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
This allows to recover the type of a term
```agda
  type-of : ∀{ℓ} {A : Set ℓ} → A → Set ℓ
  type-of {ℓ} {A} x = A
```
then, open the module to expose the names in it:
```agda
open convenience public
```
