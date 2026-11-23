import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.JoinCoordMidVar
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.JoinCoordAssocVar
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ScaledRankOneLeStandardRankOne
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyBridgeFull
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

variable {K K' K₂ : Type}

def midSwapBlocks : K ⊕ (K₂ ⊕ K') ≃ K ⊕ (K' ⊕ K₂) :=
  Equiv.sumCongr (Equiv.refl K) (Equiv.sumComm K₂ K')

def midSwapVars (ι : K → Type) (ι' : K' → Type) (ι₂ : K₂ → Type) :
    (Σ k : K ⊕ (K₂ ⊕ K'), Sum.elim ι (Sum.elim ι₂ ι') k) ≃
      (Σ k : K ⊕ (K' ⊕ K₂), Sum.elim ι (Sum.elim ι' ι₂) k) where
  toFun
    | ⟨.inl k, i⟩ => ⟨.inl k, i⟩
    | ⟨.inr (.inl k), i⟩ => ⟨.inr (.inr k), i⟩
    | ⟨.inr (.inr k), i⟩ => ⟨.inr (.inl k), i⟩
  invFun
    | ⟨.inl k, i⟩ => ⟨.inl k, i⟩
    | ⟨.inr (.inl k), i⟩ => ⟨.inr (.inr k), i⟩
    | ⟨.inr (.inr k), i⟩ => ⟨.inr (.inl k), i⟩
  left_inv := by
    rintro ⟨k | k | k, i⟩ <;> rfl
  right_inv := by
    rintro ⟨k | k | k, i⟩ <;> rfl

theorem midSwapVars_fst {ι : K → Type} {ι' : K' → Type} {ι₂ : K₂ → Type}
    (v : Σ k : K ⊕ (K₂ ⊕ K'), Sum.elim ι (Sum.elim ι₂ ι') k) :
    (midSwapVars ι ι' ι₂ v).1 = midSwapBlocks v.1 := by
  obtain ⟨k | k | k, i⟩ := v <;> rfl

theorem joinCoord_comp_midSwapVars {ι : K → Type} {ι' : K' → Type} {ι₂ : K₂ → Type} {Ω : Type*}
    (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) (w : (Σ k, ι₂ k) → Ω) :
    joinCoord x (joinCoord z w) ∘ midSwapVars ι ι' ι₂ = joinCoord x (joinCoord w z) := by
  funext v
  obtain ⟨k | k | k, i⟩ := v <;> rfl

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IFamily IsFieldIntersection)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (IsVertDiv mcIdeal joinCoord fnField pairNum midSwapBlocks midSwapVars
  ptCoord ptIdx unif)

def PairNumberRelabelAlt.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K₁ : Type) [Fintype K₁] (ι₁ : K₁ → Type) [∀ k, Fintype (ι₁ k)]
    (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)]
    (e : K₁ ≃ K₂) (σ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k)), (∀ v, (σ v).1 = e v.1) →
    ∀ (y : (Σ k, ι₂ k) → Ω) (d : ℕ),
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (y ∘ σ)) d →
        IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O y) d ∧ fnField O y = fnField O (y ∘ σ) ∧
        (∀ (b : K₂ → ℤ) (f g : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι₁),
          IsVertDiv O (mcIdeal O (y ∘ σ)) (b ∘ e) f g →
            IsVertDiv O (mcIdeal O y) b (rename σ f) (rename σ g)) ∧
        ∀ (I₁ : IFamily (IsLocalRing.ResidueField O) ι₁) (I : IFamily (IsLocalRing.ResidueField O) ι₂),
          IsFieldIntersection I₁ → IsFieldIntersection I →
        ∀ (n : ℕ) (a a' : Fin n → K₂ → ℤ) (f g : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι₁),
          (∀ i, IsVertDiv O (mcIdeal O (y ∘ σ)) (a i ∘ e - a' i ∘ e) (f i) (g i)) →
        ∀ H : MvPolynomial (Fin n) ℤ, H.IsHomogeneous (d + 1) →
          pairNum O I₁ (mcIdeal O (y ∘ σ)) d (fun i => a i ∘ e) (fun i => a' i ∘ e) f g H =
            pairNum O I (mcIdeal O y) d a a' (fun i => rename σ (f i)) (fun i => rename σ (g i)) H

end GroundTheory.Heights₂.Heights.NumbersDVR
