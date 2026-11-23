import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsComponentResBadNull
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def ComponentResFibreFinite.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (W : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (R : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Res ι W e)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsArithVar P (e + 1) → W ∈ (P.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes →
    IsGoodProj P Ψ →
    ∀ y, (resProj R Ψ ⁻¹' {y} \ resBad R Ψ).Finite

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
