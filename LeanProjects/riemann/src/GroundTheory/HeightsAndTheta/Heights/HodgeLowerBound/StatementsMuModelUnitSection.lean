import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsMuModelTrivialSection
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree

open ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

open Classical in

def MuModelUnitSection.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentDataHodge II Ψ K ι Ω E) (P : PlueckerData D)
    (H : HodgeData D.toComponentData), (∀ τ, H.F τ = D.F τ) →
    ∃ (bf bg : MuBlocks D → ℕ) (f g : MvPolynomial (Σ k : MuBlocks D, ιMu P k) ℚ),
      GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog f bf ∧
      GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog g bg ∧
      f ∉ (PXmu P).map (MvPolynomial.map (Int.castRingHom ℚ)) ∧
      g ∉ (PXmu P).map (MvPolynomial.map (Int.castRingHom ℚ)) ∧
      (∀ k, (bf k : ℤ) - bg k = muDeg D k - Sum.elim H.aMu (0 : Ψ ⊕ Ψ → ℤ) k) ∧
      ∀ W : Ideal (MvPolynomial (Σ k : MuBlocks D, ιMu P k) ℚ), W.IsPrime →
        (PXmu P).map (MvPolynomial.map (Int.castRingHom ℚ)) ≤ W →
        GroundTheory.Heights₂.Heights.NumbersDVR.IsRelevant W →
        ∃ u v : MvPolynomial (Σ k : MuBlocks D, ιMu P k) ℚ, u ∉ W ∧ v ∉ W ∧
          u * f - v * g ∈ (PXmu P).map (MvPolynomial.map (Int.castRingHom ℚ))

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree
