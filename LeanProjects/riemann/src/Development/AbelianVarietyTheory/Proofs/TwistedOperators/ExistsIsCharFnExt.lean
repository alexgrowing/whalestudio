import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacterSUTrivialTwo
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SquareIntegrableIffExtension
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UjMatScalarMul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatCoordScalarMul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetUnitScalarMul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AvgCharEqOfExt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousAtDetRootOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AestronglyMeasurableExtChar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocallyIntegrableExtChar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocallyIntegrableSnd

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.OpTrace GlobalTheory.HCChar GlobalTheory.SUChar
open GlobalTheory.Orb (ujMat ujRep CcMat IsCharFn IsRegSS)
open GlobalTheory.DSSU (SUJ SUset Ext)
open GlobalTheory.SqIntSU (scalarMul circleHaar)

noncomputable section

namespace GlobalTheory.ExtChar

theorem exists_isCharFn_ext : ∀ (n : ℕ), 1 ≤ n → ∀ (ε : Fin n → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (μ' : Measure (SUJ ε)) [μ'.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (m : ℤ) (π' π : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)) (h' : IsURepOn (SUset ε) π') (h : IsURepOn (UJset ε) π), Ext ε m π' π → ∀ Θ' : SUJ ε → ℂ, IsCharFn (suMat ε) μ' (suRep h') Θ' → ∃ Θ : UJ ε → ℂ, IsCharFn (ujMat ε) μ (ujRep h) Θ ∧ ∀ (z : Circle) (g : SUJ ε), IsRegSS (suMat ε g) → Θ (scalarMul ε (z, g)) = (z : ℂ) ^ m * Θ' g := by
  intro n hn ε μ _ μ' _ V _ _ _ m π' π h' h hE Θ' hΘ'
  haveI : NeZero n := ⟨by omega⟩
  letI := GlobalTheory.SqIntSU.circleBorelMS
  obtain ⟨c, hc0, hμ, hop⟩ := GlobalTheory.ScalarTwist.scalar_twist n hn ε μ μ'
  have hmeas := GlobalTheory.ExtChar.aestronglyMeasurable_extChar n ε μ' m Θ' hΘ'.1.aestronglyMeasurable
  have hli := GlobalTheory.ExtChar.locallyIntegrable_extChar n ε μ' m Θ' hΘ'.1 hmeas
  refine ⟨GlobalTheory.ExtChar.extChar ε m Θ', ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hμ]
    intro x
    obtain ⟨s, hs, hi⟩ := hli x
    exact ⟨s, hs, by rw [IntegrableOn, Measure.restrict_smul]; exact hi.smul_measure ENNReal.coe_ne_top⟩
  · exact GlobalTheory.ExtCharCont.continuousAt_extChar n ε m Θ' hΘ'.2.1
  · intro f hf
    have hfc : Continuous f := GlobalTheory.Orb.continuous_of_mem_ccSmooth (isInducing_matCoord (ε := ε)).continuous hf
    rw [hop V m π' π h' h hE f hfc hf.1]
    have ht := hΘ'.2.2 _ (GlobalTheory.CentreAvg.avg_mem_ccMat n ε m f hf)
    refine ⟨ht.1.smul _, ?_⟩
    rw [OpTrace.trace_smul, ht.2, hμ, integral_smul_nnreal_measure, GlobalTheory.ExtCharInt.integral_extChar n ε μ' m Θ' hΘ'.1 hli f hfc hf.1,
      NNReal.smul_def, Complex.real_smul]
  · intro z g hg
    rw [GlobalTheory.ExtChar.extChar_scalarMul, GlobalTheory.ExtChar.avgChar_eq_of_ext n ε μ' V m π' π h' hE Θ' hΘ' g hg]

end GlobalTheory.ExtChar
