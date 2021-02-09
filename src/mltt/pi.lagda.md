---
title: "Pi types"
subtitle: "Martin-Löf Type Theory"
description: "A minimal Type Theory in Martin-Löf style: Pi types"
---

### Contents {#top}


--------------------------------------------------------------------------------

```agda
{-# OPTIONS --without-K --safe #-}

module mltt.pi where

open import level renaming (zero to lzero; suc to lsuc)
open import mltt.sigma
```

Π-types are built=in in Agda, with the notation ∀ (x : A) → E x

```agda
Π : ∀ {ℓ ℓ'} (B : Set ℓ) (E : B → Set ℓ') → Set (ℓ ⊔ ℓ') 
Π B E = (x : B) → E x

data Π′ {ℓ ℓ' : Level} (B : Set ℓ) (E : B → Set ℓ') : Set (ℓ ⊔ ℓ') where
  dfun : ((x : B) → E x) → Π′ B E

syntax Π B (λ x → E) = Π[ x ∈ B ] E
syntax Π′ B (λ x → E) = Π′[ x ∈ B ] E
```

Tautological elimination rules:

```agda
Π-elim : ∀ {ℓ ℓ'} {B : Set ℓ} {E : B → Set ℓ'} {b : B} → Π B E → E b
Π-elim {b = b} f = f b

Π′-elim : ∀ {ℓ ℓ'} {B : Set ℓ} {E : B → Set ℓ'} {b : B} → Π′ B E → E b
Π′-elim {b = b} (dfun f) = f b

-- Same thing, but sometimes more convenient
Π′-elim₁ : ∀ {ℓ ℓ'} {B : Set ℓ} {E : B → Set ℓ'} → Π′ B E → (b : B) → E b 
Π′-elim₁ (dfun f) b = f b
```


```agda
-- This, and the mltt.sigma import above need to go
-- THey are here just for compatibility due to a call
-- in basichomotopy.lagda.md
Γ : ∀ {ℓ ℓ'} {B : Set ℓ} {E : B → Set ℓ'} → Π B E → (B → Σ B E)
Γ f b = b , f b
```
