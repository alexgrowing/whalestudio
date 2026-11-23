import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumePerRankLeNegSlopeScaled
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.QuotientMetricDivisors.Statement
import Formalism.MeanHeightDescent.DivisionInequalityWithCovolume
import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.MeasureFailsForLargeConstant
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covolumePerRank_le_neg_slope_scaled : ∀ (K V : Type) [Field K] [NumberField K] [IsTotallyComplex K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (N : (K →+* ℂ) → V → ℝ), GlobalTheory.AllWt.HasGram N →
    ∀ (L : Submodule (𝓞 K) V) (d : ℕ), 0 < d → ∀ (b : Fin d → V), LinearIndependent K b →
    (∀ x ∈ L, x ∈ Submodule.span K (Set.range b)) →
    ∀ (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (s : ℝ), 0 < s → s ≤ 1 → (∀ v, IsUnit (X v).det) →
    (∀ v (c : Fin d → K), Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin d)) X v c = s * N v.embedding (∑ k, c k • b k)) →
    Submodule.IsLattice K (L.comap ((Fintype.linearCombination K b).restrictScalars (𝓞 K))) →
    Formalism.DivisionValues.lcv X (L.comap ((Fintype.linearCombination K b).restrictScalars (𝓞 K))) / (d : ℝ) ≤ -GlobalTheory.AllWt.slope_sq N L := by
  first | exact @GlobalTheory.CovolCore.lcv_div_le_neg_slope_sq | exact GlobalTheory.CovolCore.lcv_div_le_neg_slope_sq | (intros; apply GlobalTheory.CovolCore.lcv_div_le_neg_slope_sq <;> assumption)
