---
title: "2-categorical constructions"
description: "Ap2: two cell version of ap"
---

```agda
{-# OPTIONS --without-K --safe #-}

module homotopy.twocatconstructions.ap2 where

open import level
open import mltt.identity
open import homotopy.twocatconstructions.core

open ◾-lemmas
open ap-lemmas
open ≡-Reasoning
```

```agda
ap2 : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) {x y : A} {p q : x ≡ y} → 
      p ≡ q → (ap f p ) ≡ (ap f q)
ap2 f {p = p} refl = idp (ap f p)
```

```agda
module ap2-lemmas where

  module _ {ℓ ℓ' : Level} {A : Set ℓ} {B : Set ℓ'}
                          (f : A → B) {x y : A} where

    ap2◾ : {p q r : x ≡ y} (α : p ≡ q) (β : q ≡ r) →
           ap2 f (α ◾ β) ≡ (ap2 f α) ◾ (ap2 f β)
    ap2◾ refl β = refl

  module _ {ℓ ℓ' : Level} {A : Set ℓ} {B : Set ℓ'}
                          (f : A → B) {x y z : A} where

    ap2◾ʳ : {p q : x ≡ y} (α : p ≡ q) (r : y ≡ z) →
            (ap2 f (α ◾ʳ r)) ◾ (ap◾ f q r) 
            ≡ (ap◾ f p r) ◾ ( (ap2 f α) ◾ʳ (ap f r) )
    ap2◾ʳ {p} refl r = (ru (ap◾ f p r)) ⁻¹


    ap2◾ˡ : (q : x ≡ y) {r s : y ≡ z} (β : r ≡ s) →
            (ap2 f (q ◾ˡ β)) ◾ (ap◾ f q s)
            ≡ (ap◾ f q r) ◾ ( (ap f q) ◾ˡ (ap2 f β))
    ap2◾ˡ q {r} {.r} refl = (ru (ap◾ f q r)) ⁻¹

    ap2★ : {p q : x ≡ y} {r s : y ≡ z} (α : p ≡ q) (β : r ≡ s) →
           ap2 f (α ★ β) ◾ (ap◾ f q s) ≡ (ap◾ f p r) ◾ ((ap2 f α) ★ (ap2 f β))
    ap2★ {p} {q} {r} {s} α β = begin
               ap2 f (α ★ β) ◾ (ap◾ f q s)                ≡⟨ refl ⟩
               ap2 f ((α ◾ʳ r) ◾ (q ◾ˡ β)) ◾ (ap◾ f q s)  ≡⟨ ( ap2◾ f (α ◾ʳ r) (q ◾ˡ β) ) ◾ʳ (ap◾ f q s) ⟩
               ((ap2 f (α ◾ʳ r)) ◾ (ap2 f (q ◾ˡ β))) ◾ (ap◾ f q s)      ≡⟨ assoc (ap2 f (α ◾ʳ r)) _ _ ⟩
               ap2 f (α ◾ʳ r) ◾ ((ap2 f (q ◾ˡ β)) ◾ (ap◾ f q s))        ≡⟨ ap2 f (α ◾ʳ r) ◾ˡ ap2◾ˡ q β ⟩
               ap2 f (α ◾ʳ r) ◾ ((ap◾ f q r) ◾ ((ap f q) ◾ˡ (ap2 f β))) ≡⟨ (assoc (ap2 f (α ◾ʳ r)) _ _ ) ⁻¹ ⟩
               (ap2 f (α ◾ʳ r) ◾ (ap◾ f q r)) ◾ ((ap f q) ◾ˡ (ap2 f β)) ≡⟨ (ap2◾ʳ α r) ◾ʳ ((ap f q) ◾ˡ (ap2 f β)) ⟩
               ((ap◾ f p r) ◾ ( (ap2 f α) ◾ʳ (ap f r))) ◾ ((ap f q) ◾ˡ (ap2 f β))   ≡⟨ assoc (ap◾ f p r) _ _ ⟩
               (ap◾ f p r) ◾ ((( (ap2 f α) ◾ʳ (ap f r))) ◾ ((ap f q) ◾ˡ (ap2 f β))) ≡⟨ refl ⟩
               (ap◾ f p r) ◾ ((ap2 f α) ★ (ap2 f β))                                 ∎


    ap2★′ : {p q : x ≡ y} {r s : y ≡ z} (α : p ≡ q) (β : r ≡ s) →
             ap2 f (α ★′ β) ◾ (ap◾ f q s) ≡ (ap◾ f p r) ◾ ((ap2 f α) ★′ (ap2 f β))
    ap2★′ {p} {q} {r} {s} α β = begin
              ap2 f (α ★′ β) ◾ (ap◾ f q s) ≡⟨ refl ⟩
              ap2 f ((p ◾ˡ β) ◾ (α ◾ʳ s)) ◾ (ap◾ f q s) ≡⟨ (ap2◾ f (p ◾ˡ β) (α ◾ʳ s)) ◾ʳ (ap◾ f q s) ⟩
              (ap2 f (p ◾ˡ β) ◾ ap2 f (α ◾ʳ s)) ◾ (ap◾ f q s)          ≡⟨ assoc (ap2 f (p ◾ˡ β)) _ _ ⟩
              ap2 f (p ◾ˡ β) ◾ (ap2 f (α ◾ʳ s) ◾ ap◾ f q s)            ≡⟨ ap2 f (p ◾ˡ β) ◾ˡ ap2◾ʳ α s ⟩
              ap2 f (p ◾ˡ β) ◾ ((ap◾ f p s) ◾ ((ap2 f α) ◾ʳ (ap f s))) ≡⟨ (assoc (ap2 f (p ◾ˡ β)) _ _ ) ⁻¹  ⟩
              (ap2 f (p ◾ˡ β) ◾ (ap◾ f p s)) ◾ ((ap2 f α) ◾ʳ (ap f s)) ≡⟨ (ap2◾ˡ p β) ◾ʳ ((ap2 f α) ◾ʳ (ap f s)) ⟩
              ((ap◾ f p r) ◾ (ap f p ◾ˡ ap2 f β)) ◾ ((ap2 f α) ◾ʳ (ap f s)) ≡⟨ assoc (ap◾ f p r) _ _ ⟩
              (ap◾ f p r) ◾ ((ap f p ◾ˡ ap2 f β) ◾ ((ap2 f α) ◾ʳ (ap f s))) ≡⟨ refl ⟩
              (ap◾ f p r) ◾ ((ap2 f α) ★′ (ap2 f β))                        ∎
```
