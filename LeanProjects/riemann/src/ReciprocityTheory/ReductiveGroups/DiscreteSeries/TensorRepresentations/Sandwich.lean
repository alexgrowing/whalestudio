import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Residue
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Transported
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.SandwichA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiExistsStatement
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

open MeasureTheory

theorem fdeg_ratio_V {ε : Fin n → Bool} (hp : 1 ≤ pOf ε) (hq : 1 ≤ qOf ε) {μ : Fin n → ℝ}
    (hμ : S7.IsHCParam μ) {h : ℝ} (hgap : GapAtLeast ε μ h) (hh : thrStar ε + 1 < h) (s : Fin n)
    (hs : StrictAnti (μ + Pi.single s 1))
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : Formalism.MainNotions.S.IsDS ε μ σ)
    {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] {σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')}
    (hσ' : Formalism.MainNotions.S.IsDS ε (μ + Pi.single s 1) σ')
    (ν : Measure (Formalism.REAL.UJ ε)) (hν : ν.IsHaarMeasure) {d : ℝ} (hd : Formalism.MainNotions.S.IsFdeg ν σ d) :
    Formalism.MainNotions.S.IsFdeg ν σ' (d * ratioV μ s) := by
  exact swC_main false hp hq hμ hgap hh s hs hσ hσ' ν hν hd

end ReciprocityTheory.ChartRestriction.DS
