import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsComponentResBadNull
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def ComponentResFibreSum.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (L : Fin e → HermLine ι) (W : Ideal (MvPolynomial (Σ k, ι k) ℂ))
    (R : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Res ι W e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsArithVar P (e + 1) → (∀ j, IsSmoothHerm (L j)) →
    W ∈ (P.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes → IsGoodProj P Ψ →
    ∀ᵐ y, ∑ᶠ w ∈ fibre P Ψ y,
        sheetDensity P Ψ (pot L) ((mcPts P ∩ zeroLocus ℂ W).indicator fun _ => (1 : ℝ)) y w =
      ∑ᶠ x ∈ resProj R Ψ ⁻¹' {y} \ resBad R Ψ,
        ReciprocityTheory.AnForm.M.pushDens R.atlas
          (fun j => R.pot (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.logH (L j))) (resProj R Ψ) x

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
