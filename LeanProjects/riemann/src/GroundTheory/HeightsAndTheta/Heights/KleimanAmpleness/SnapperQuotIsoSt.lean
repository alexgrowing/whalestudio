import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SnapperCutObj
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w v'

section Defs

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

structure QuotIso {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    {E' : Type v'} [AddCommGroup E'] [Module Ω E'] [Module S E'] [IsScalarTower S Ω E']
    (F₁ F₂ : SubSystem S x E) (G₁ G₂ : SubSystem S x E') where

  equiv : ∀ I : Chart x,
    (F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) ≃ₗ[S] (G₁.sub I ⧸ SubSystem.quotSub G₁ G₂ I)

  comm : ∀ (I J : Chart x) (h : I.1 ⊆ J.1) (y : F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I),
    equiv J (SubSystem.quotRes F₁ F₂ I J h y) = SubSystem.quotRes G₁ G₂ I J h (equiv I y)

def QuotIso.refl {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    (F₁ F₂ : SubSystem S x E) : QuotIso F₁ F₂ F₁ F₂ where
  equiv _ := LinearEquiv.refl S _
  comm _ _ _ _ := rfl

end Defs

def SnapperQuotIso.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (E : Type v) [AddCommGroup E] [Module Ω E] [Module k E] [IsScalarTower k Ω E]
    (E' : Type v') [AddCommGroup E'] [Module Ω E'] [Module k E'] [IsScalarTower k Ω E']
    (F₁ F₂ : SubSystem k x E) (G₁ G₂ : SubSystem k x E'), QuotIso F₁ F₂ G₁ G₂ →
    eulerCharQuot k F₁ F₂ = eulerCharQuot k G₁ G₂

def snapperQuotIso_hyps (k : Type u) [Field k] :
    QuotIso (twistSys k (genericPt k 1) 0)
      ((twistSys k (genericPt k 1) 0).twist (idealSys (genericPt k 1) (primeOf (S := k) (genericPt k 1))))
      (twistSys k (genericPt k 1) 0)
      ((twistSys k (genericPt k 1) 0).twist (idealSys (genericPt k 1) (primeOf (S := k) (genericPt k 1)))) :=
  QuotIso.refl _ _

end

end GroundTheory.Heights₂.Heights.Kleiman
