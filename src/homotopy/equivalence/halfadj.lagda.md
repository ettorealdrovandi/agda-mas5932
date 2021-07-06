---
title: "Half adjoint equivalences"
description: "Invertibility data are supplemented with higher homotopies
---

### Contentes {#top}

1. [Half adjoint equivalences](#hadj)
1. [Half adjoint equivalences are isomorphisms](#eq-to-iso)
1. [Identity is a weak equivalence](#id-is-eq})
1. [Standard properties and reasoning](#eq-reason)

--------------------------------------------------

```agda
{-# OPTIONS --without-K --safe #-}

module homotopy.equivalence.halfadj where

open import mltt
open import function
open import hlevels
open import homotopy.retraction
open import homotopy.fibrations
open import homotopy.naturality
open import homotopy.twocatconstructions

open ≡-Reasoning
open ◾-lemmas
open ~-lemmas
open ap-lemmas
```

### Half adjoint equivalences {#hadj}

Take a quasi-invertible function and supplement its invertibility data
with a higher homotopy. Let:

    f : A → B
    g : B → A
    ε : f ∘ g ~ id
    η : g ∘ f ~ id

Following a standard argument from the theory of adjunctions in
Category Theory, we have two possible homotopies:

    ε ∘~ f : f ∘ g ∘ f ~ f
    f ~∘ η : f ∘ g ∘ f ~ f

Rather than leaving them unconstrained, we consider a higher homotopy between the two:

    τ : f ~∘ η  ≈ ε ~∘ f 

We define the type of a function being a half adjoint equivalence and
the corresponding type of half adjoint equivalences:

```agda
ishaeq : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) → Set (ℓ ⊔ ℓ')
ishaeq f = Σ[ g ∈ (codomain f → domain f) ]
           Σ[ ε ∈ (f ∘′ g ~ id) ]
           Σ[ η ∈ (g ∘′ f ~ id) ] 
           Π[ x ∈ domain f ] (ap f (η x) ≡ ε (f x))

is-haeq = ishaeq

_≃h_  : ∀ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') → Set (ℓ ⊔ ℓ')
A ≃h B = Σ[ f ∈ (A → B) ] (ishaeq f)
```

### Half adjoint equivalences are isomorphisms {#eq-to-iso}

```agda
module _ {ℓ ℓ'}{A : Set ℓ}{B : Set ℓ'} where

  open _≅_
  ≃h→≅ : A ≃h B → A ≅ B
  to (≃h→≅ (f , g , ε , η , τ)) = f
  from (≃h→≅ (f , g , ε , η , τ)) = g
  _≅_.ε (≃h→≅ (f , g , ε , η , τ)) = ε
  _≅_.η (≃h→≅ (f , g , ε , η , τ)) = η

  -- This is for compatibility with a previous version of this development
  haeq→qinv : (f : A → B) → ishaeq f → qinv f
  haeq→qinv f is = record { inv = from (≃h→≅ (f , is)) 
                          ; ε = ε (≃h→≅ (f , is))
                          ; η = η (≃h→≅ (f , is)) }

  ≅→≃h : A ≅ B → A ≃h B
  π₁ (≅→≃h (hoeq f g ε η)) = f
  π₁ (π₂ (≅→≃h (hoeq f g ε η))) = g
  π₁ (π₂ (π₂ (≅→≃h (hoeq f g ε η)))) y = f (g y) ≡⟨ ε (f (g y)) ⁻¹ ⟩
                                         f (g (f (g y))) ≡⟨ ap f (η (g y)) ⟩
                                         f (g y) ≡⟨ ε y ⟩
                                         y ∎
  π₁ (π₂ (π₂ (π₂ (≅→≃h (hoeq f g ε η))))) = η
  π₂ (π₂ (π₂ (π₂ (≅→≃h (hoeq f g ε η))))) x = ap f (η x) ≡⟨ refl ⟩
                        refl ◾ ap f (η x) ≡⟨ ap (_◾ (ap f (η x)) )  ( linv (ε (f (g (f x) ) )) ) ⁻¹   ⟩
                        ((ε (f (g (f x) ) )) ⁻¹ ◾ ε (f (g (f x) ) )) ◾ ap f (η x) ≡⟨ assoc ((ε (f (g (f x) ) )) ⁻¹)  (ε (f (g (f x) ) ))  (ap f (η x))  ⟩
                        (ε (f (g (f x) ) )) ⁻¹ ◾ ( ε (f (g (f x) ) ) ◾ ap f (η x)) ≡⟨ ap ( (ε (f (g (f x))) ⁻¹) ◾_ ) (lem1 x) ⟩
                        (ε (f (g (f x) ) )) ⁻¹ ◾ (( ap (f ∘′ g)  (ap f (η x)) ) ◾ ε (f x) ) ≡⟨ ap ( (ε (f (g (f x))) ⁻¹) ◾_ ) (lem2 x)  ⟩
                        (ε (f (g (f x) ) )) ⁻¹ ◾ ( ap f (η (g (f x))) ◾ ε (f x) ) ≡⟨ ap (ε (f (g (f x))) ⁻¹ ◾_ ) (lem3 x) ⟩
                        ε̃ (f x) ∎
                            where

                              
                              lem1 = λ x → (ε (f (g (f x))) ◾ ap f (η x)) ≡⟨ homot-natural (λ x₁ → ε(f x₁)) (η x)  ⟩
                                           ap (λ z → f (g (f z))) (η x) ◾ ε (f x) ≡⟨ ap (_◾ (ε (f x))) (lem1-1 x) ⟩
                                           (ap (λ x₁ → f (g x₁)) (ap f (η x)) ◾ ε (f x)) ∎
                                             where
                                               lem1-1 = λ x → ap (λ z → f (g (f z))) (η x) ≡⟨ ap∘ f (f ∘′ g) (η x) ⟩
                                                               ap (λ x₁ → f (g x₁)) (ap f (η x)) ∎
                              lem2 = λ x → (ap (λ x₁ → f (g x₁)) (ap f (η x)) ◾ ε (f x)) ≡⟨ ap (_◾ (ε (f x))) (lem2-1 x)  ⟩
                                           (ap f (η (g (f x))) ◾ ε (f x)) ∎
                                              where
                                                lem2-1 = let natη = corollary[homot-natural] in
                                                             λ x → ap (λ x₁ → f (g x₁)) (ap f (η x)) ≡⟨ (ap∘ f (f ∘′ g) (η x)) ⁻¹ ⟩
                                                                   ap (λ x₁ → f (g (f x₁))) (η x) ≡⟨ ap∘ (g ∘′ f) f (η x) ⟩
                                                                   ap f (ap (g ∘′ f) (η x)) ≡⟨ ap2 f ((natη η {x}) ⁻¹) ⟩
                                                                   ap f (η (g (f x))) ∎ 
                              ε̃ = π₁ (π₂ (π₂ (≅→≃h (hoeq f g ε η)))) 
                              lem3 = λ x → (ap f (η (g (f x))) ◾ ε (f x)) ≡⟨ ap ((ap f (η (g (f x)))) ◾_ ) (ru (ε (f x))) ⁻¹ ⟩
                                           (ap f (η (g (f x))) ◾ (ε (f x) ◾ refl)) ∎
```

### Identity is a weak equivalence {#id-is-eq}

```agda
ishaeq-id : ∀ {ℓ} {A : Set ℓ} → is-haeq (𝓲𝓭 A)
π₁ ishaeq-id = id
π₁ (π₂ ishaeq-id) = λ x → refl
π₁ (π₂ (π₂ ishaeq-id)) = λ x → refl
π₂ (π₂ (π₂ ishaeq-id)) = λ x → refl
```

### Standard properties and reasoning {#eq-reason}

The type `A ≃h B` satisfies the standard equivalence relation
properties. We use this to build a "Reasoning" module.

**Note:** Transitivity is superseded and subsumed by the
  "two-out-of-three" property, which is proved elsewhere in this
  development.

```agda
module ≃h-lemmas where

  open ≅-lemmas

  refl-≃h : ∀ {ℓ} {A : Set ℓ} → A ≃h A
  refl-≃h = id , ishaeq-id

  ≃h-sym : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → A ≃h B → B ≃h A
  ≃h-sym (f , is) = let φ = ≃h→≅ (f , is) 
                    in ≅→≃h (φ ≅⁻¹)

  ≃h-trans : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : Set ℓ'} {C : Set ℓ''} →
             A ≃h B → B ≃h C → A ≃h C
  π₁ (≃h-trans (f , i) (g , j)) = g ∘′ f
  π₁ (π₂ (≃h-trans (f , i) (g , j))) = f⁻¹ ∘′ g⁻¹
    where
      f⁻¹ = π₁ i
      g⁻¹ = π₁ j
  π₁ (π₂ (π₂ (≃h-trans (f , i) (g , j)))) x = g (f (f⁻¹ (g⁻¹ x))) ≡⟨ ap g (ε (g⁻¹ x)) ⟩
                                              g (g⁻¹(x))          ≡⟨ ε' x ⟩
                                              x ∎
    where
      f⁻¹ = π₁ i
      g⁻¹ = π₁ j
      ε = π₁ (π₂ i)
      ε' = π₁ (π₂ j)

  π₁ (π₂ (π₂ (π₂ (≃h-trans (f , i) (g , j))))) x = f⁻¹ (g⁻¹ (g (f (x)))) ≡⟨ ap f⁻¹ (η' (f x)) ⟩
                                                   f⁻¹ (f (x))           ≡⟨ η x ⟩
                                                   x ∎
    where
      f⁻¹ = π₁ i
      g⁻¹ = π₁ j
      η = π₁ (π₂ (π₂ i))
      η' = π₁ (π₂ (π₂ j))

  -- boneheaded computation    
  π₂ (π₂ (π₂ (π₂ (≃h-trans (f , i) (g , j))))) x = begin
     ap (g ∘′ f) (ap f⁻¹ (η' (f x)) ◾ (η x ◾ refl))                  ≡⟨ ap∘ f g _ ⟩
     ap g (ap f (ap f⁻¹ (η' (f x)) ◾ (η x ◾ refl)))                  ≡⟨ ap2 g (ap◾ f p q) ⟩
     ap g (ap f (ap f⁻¹ (η' (f x))) ◾ ap f (η x ◾ refl))             ≡⟨ ap◾ g _ s ⟩
     ap g (ap f (ap f⁻¹ (η' (f x)))) ◾ ap g (ap f (η x ◾ refl))      ≡⟨ _ ◾ˡ (ap2 g (ap◾ f (η x) refl)) ⟩
     ap g (ap f (ap f⁻¹ (η' (f x)))) ◾ ap g (ap f (η x) ◾ ap f refl) ≡⟨ ap2 g (ap∘ f⁻¹ f _ ) ⁻¹ ◾ʳ (ap g (ap f (η x) ◾ refl)) ⟩
     ap g (ap (f ∘′ f⁻¹) (η' (f x))) ◾ ap g (ap f (η x) ◾ refl)      ≡⟨ ap2 g (ru t) ⁻¹ ◾ʳ _ ⟩
     ap g (ap (f ∘′ f⁻¹) (η' (f x)) ◾ refl) ◾ ap g (ap f (η x) ◾ refl)                    ≡⟨ ap2 g (t ◾ˡ ((rinv (ε (f x))) ⁻¹)) ◾ʳ _  ⟩
     ap g (ap (f ∘′ f⁻¹) (η' (f x)) ◾ (ε (f x) ◾ ε (f x) ⁻¹)) ◾ ap g (ap f (η x) ◾ refl)  ≡⟨ ap2 g (assoc t _ _) ⁻¹ ◾ʳ _ ⟩
     ap g ((ap (f ∘′ f⁻¹) (η' (f x)) ◾ ε (f x)) ◾ ε (f x) ⁻¹) ◾ ap g (ap f (η x) ◾ refl)  ≡⟨ ap2 g ((homot-natural' ε r) ◾ʳ ε (f x) ⁻¹) ◾ʳ _ ⟩
     ap g ((ε (g⁻¹ (g (f x))) ◾ (ap id (η' (f x)))) ◾ ε (f x) ⁻¹) ◾ ap g (ap f (η x) ◾ refl)  ≡⟨ ap2 g ((u ◾ˡ apid r) ◾ʳ ε (f x) ⁻¹) ◾ʳ _ ⟩
     ap g ((ε (g⁻¹ (g (f x))) ◾ (η' (f x))) ◾ ε (f x) ⁻¹) ◾ ap g (ap f (η x) ◾ refl)          ≡⟨ (ap◾ g (u ◾ r) _) ◾ʳ _ ⟩
     (ap g (ε (g⁻¹ (g (f x))) ◾ (η' (f x))) ◾ ap g (ε (f x) ⁻¹)) ◾ ap g (ap f (η x) ◾ refl)   
                                                                      ≡⟨ assoc (ap g (ε (g⁻¹ (g (f x))) ◾ (η' (f x)))) _ _  ⟩
     (ap g (ε (g⁻¹ (g (f x))) ◾ (η' (f x)))) ◾ (ap g (ε (f x) ⁻¹) ◾ ap g (ap f (η x) ◾ refl))   ≡⟨ (ap◾ g u r) ◾ʳ _ ⟩
     (ap g (ε (g⁻¹ (g (f x)))) ◾ ap g (η' (f x))) ◾ (ap g (ε (f x) ⁻¹) ◾ ap g (ap f (η x) ◾ refl))   ≡⟨ ( (ap g u) ◾ˡ τ' (f x) ) ◾ʳ _ ⟩
     (ap g (ε (g⁻¹ (g (f x)))) ◾ ε' (g (f x))) ◾ (ap g (ε (f x) ⁻¹) ◾ ap g (ap f (η x) ◾ refl))
                                                                      ≡⟨ (ap g (ε (g⁻¹ (g (f x)))) ◾ ε' (g (f x))) ◾ˡ (ap◾ g (ε (f x) ⁻¹) _) ⁻¹ ⟩
     (ap g (ε (g⁻¹ (g (f x)))) ◾ ε' (g (f x))) ◾ ap g (ε (f x) ⁻¹ ◾  (ap f (η x) ◾ refl))       ≡⟨ _ ◾ˡ ap2 g (assoc (ε (f x) ⁻¹) _ _) ⁻¹ ⟩
     (ap g (ε (g⁻¹ (g (f x)))) ◾ ε' (g (f x))) ◾ ap g ((ε (f x) ⁻¹ ◾  ap f (η x)) ◾ refl)       ≡⟨ _ ◾ˡ ap2 g ((ε (f x) ⁻¹ ◾ˡ τ x) ◾ʳ refl) ⟩
     (ap g (ε (g⁻¹ (g (f x)))) ◾ ε' (g (f x))) ◾ ap g ((ε (f x) ⁻¹ ◾  ε (f x)) ◾ refl)          ≡⟨ _ ◾ˡ ap2 g (linv (ε (f x)) ◾ʳ refl) ⟩
     (ap g (ε (g⁻¹ (g (f x)))) ◾ ε' (g (f x))) ◾ ap g (refl ◾ refl)                             ≡⟨ assoc (ap g u) _ refl ⟩
     ap g (ε (g⁻¹ (g (f x)))) ◾ (ε' (g (f x)) ◾ refl) ∎

     where
      f⁻¹ = π₁ i
      g⁻¹ = π₁ j
      ε = π₁ (π₂ i)
      ε' = π₁ (π₂ j)
      η = π₁ (π₂ (π₂ i))
      η' = π₁ (π₂ (π₂ j))
      τ = π₂ (π₂ (π₂ i))
      τ' = π₂ (π₂ (π₂ j))

      p = ap f⁻¹ (η' (f x))
      q = η x ◾ refl
      s = ap f (η x ◾ refl)
      r = η' (f x)
      t = ap (f ∘′ f⁻¹) (η' (f x))
      u = ε (g⁻¹ (g (f x)))

  -- Syntax declarations
  ≃h-id = refl-≃h
  syntax ≃h-sym f = f ≃h⁻¹
  syntax ≃h-trans f g = f ≃◾≃h g
  -- ---------------------------

module ≃h-Reasoning where
  
  open ≃h-lemmas

  infix 3 _≃h∎
  infixr 2 _≃h⟨_⟩_
  infix 1 begin≃h_

  begin≃h_ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} →
             A ≃h B → A ≃h B
  begin≃h p = p
  
  _≃h⟨_⟩_ : ∀ {ℓ ℓ' ℓ''} (A : Set ℓ) {B : Set ℓ'} {C : Set ℓ''} → A ≃h B → B ≃h C → A ≃h C
  A ≃h⟨ e ⟩ f = e ≃◾≃h f

  _≃h∎ : ∀ {ℓ} (A : Set ℓ) → A ≃h A
  A ≃h∎ = ≃h-id {A = A}
```


<!--
**FIXME** This should be elsewhere
-->

Equality is a weak equivalence. This is one direction (the easy one)
of the correspondence underlying the univalence principle.

```agda
transport-is-≃h : ∀ {ℓ ℓ'} {A : Set ℓ} {P : A → Set ℓ'} {x y : A}
                  (p : x ≡ y) → ishaeq (transport P p)
transport-is-≃h refl = ishaeq-id

≡→≃h : ∀ {ℓ} {A B : Set ℓ} → A ≡ B → A ≃h B
≡→≃h p = (Id→Fun p) , (transport-is-≃h p)

≡→≃h' : ∀ {ℓ} {A B : Set ℓ} → A ≡ B → A ≃h B
≡→≃h' refl = refl-≃h
  where
    open ≃h-lemmas
```

<p style="font-size: smaller; text-align: right">[top ⇑](#top)</p>
---

