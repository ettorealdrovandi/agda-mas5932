---
title: "Homotopy: retraction—Core"
description: "Definition and main properties of retractions"
---

### Contents {#top}

1. [Retractions](#retractions)
2. [Function retraction](#funretr)

```agda
{-# OPTIONS --without-K --safe #-}

module homotopy.retraction.core where

open import level
open import mltt --function is also exported from mltt, but it will go away
open import function 

```

### Retractions {#retractions}

```agda
has-sect : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → (A → B) → Set (ℓ ⊔ ℓ')
has-sect r = Σ[ s ∈ (codomain r → domain r) ] (r ∘′ s ~ id)

record _◅_ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') : Set (ℓ ⊔ ℓ') where
  field
    retr : B → A
    sect : A → B
    h : retr ∘′ sect ~ id

◅-struct-iso : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} →
               (A ◅ B) ≅ (Σ[ r ∈ (B → A) ] (has-sect r))
◅-struct-iso = record { to = λ { record { retr = r ; sect = s ; h = h } → r , s , h}
                      ; from = λ { (r , s , h) → record { retr = r ; sect = s ; h = h }}
                      ; ε = λ _ → refl
                      ; η = λ _ → refl }
```

Name the projectors for compatibility

```agda
retract : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → (A ◅ B) → (B → A)
retract record { retr = r ; sect = s ; h = h } = r

section : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → (A ◅ B) → (A → B)
section record { retr = r ; sect = s ; h = h } = s

retract-homotopy : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} 
                   (ρ : A ◅ B) → (retract ρ) ∘′ (section ρ) ~ id
retract-homotopy record { retr = r ; sect = s ; h = h } = h

retract-has-sect : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} 
                   (ρ : A ◅ B) → has-sect (retract ρ)
retract-has-sect record { retr = r ; sect = s ; h = h } = s , h
```

---

```agda
module ◅-lemmas where

  ◅-id : ∀ {ℓ} {A : Set ℓ} → (A ◅ A)
  ◅-id = record { retr = id ; sect = id ; h = λ _ → refl }

  _◅◾_ : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : Set ℓ'} {C : Set ℓ''} → 
         A ◅ B → B ◅ C → A ◅ C
  record { retr = r ; sect = s ; h = h } ◅◾ record { retr = r₁ ; sect = s₁ ; h = h₁ } =
    record { retr = r ∘′ r₁ ; sect = s₁ ∘′ s ; h = h₂ }
       where
         open ~-lemmas
         h₂ : ∀ x → r (r₁ (s₁ (s x))) ≡ x
         h₂ = (r ∘~ (h₁ ~∘ s)) ~◾~ h
```

---

```agda
module ◅-Reasoning where

  open ◅-lemmas

  infix  3 _◅∎
  infixr 2 _◅⟨_⟩_
  infix  1 begin◅_

  _◅⟨_⟩_ : ∀ {ℓ ℓ' ℓ''} (A : Set ℓ) {B : Set ℓ'} {C : Set ℓ''} → 
          A ◅ B → B ◅ C → A ◅ C
  A ◅⟨ ρ ⟩ σ = ρ ◅◾ σ

  _◅∎ : ∀ {ℓ} (A : Set ℓ) → A ◅ A
  A ◅∎ = ◅-id {A = A}

  begin◅_ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} →
            A ◅ B → A ◅ B
  begin◅ ρ = ρ
```

<p style="font-size: smaller; text-align: right">[top ⇑](#top)</p>
---


### Function retraction {#funretr}

<span style="color:teal;font-weight:bold">Definition.</span> A
function $f \colon A → X$ is a *retraction* of a function $g \colon B
→ Y$ if there is a homotopy commutative diagram

$$
\begin{array}{ccccc}
A & \longrightarrow & B & \longrightarrow & A \\
\downarrow & & \downarrow & & \downarrow \\
X & \longrightarrow & Y & \longrightarrow & X
\end{array}
$$

<--

A ⟶ B ⟶ A
↓    ↓    ↓
X ⟶ Y ⟶ X

-->

in which the top and the bottom rows are retractions. There is an
additional condition, spelling how the outer square interacts with the
retraction data: if `(r, s , ε) : A ◅ B` and `(t , u , η) : X ◅ Y`,
then we must have a witness

    H a : K (s a) ◾ ap t (ap t (L a))) ≡ ((ap f (rs a)) ◾ tu (f a) ⁻¹)


```agda
{- -- +-}
record _◅→_  {ℓ ℓ' ν ν' : Level} {A : Set ℓ} {B : Set ℓ'} {X : Set ν} {Y : Set ν'}
             (f : A → X) (g : B → Y) : Set (ℓ ⊔ ℓ' ⊔ ν ⊔ ν') where
       open _◅_

       field
         φ : A ◅ B
         ψ : X ◅ Y
         
       r : B → A
       r = retr φ

       s : A → B
       s = sect φ

       rs : r ∘′ s ~ id
       rs = h φ

       t : Y → X
       t = retr ψ

       u : X → Y
       u = sect ψ
         
       tu : t ∘′ u ~ id
       tu  = h ψ

       field
         L : g ∘′ s ~ u ∘′ f
         K : f ∘′ r ~ t ∘′ g
         H : (a : A) → (K (s a) ◾ (ap t (L a))) ≡ ((ap f (rs a)) ◾ tu (f a) ⁻¹)
-- -}
```
