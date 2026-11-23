import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumLogGaussAbsLeFractionalIdealIndex
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_log_gaussAbs_le_fractionalIdeal_index : ∀ (F : Type) [Field F] [NumberField F] (τ : Type) (g : MvPolynomial τ F), g ≠ 0 → ∀ (I : Submodule (𝓞 F) F) (δ : F), δ ≠ 0 → 1 ≤ I → (∃ c : 𝓞 F, c ≠ 0 ∧ ∀ y ∈ I, c • y ∈ (1 : Submodule (𝓞 F) F)) → (∀ m, coeff m g / δ ∈ I) → ∑ᶠ q : FinitePlace F, Real.log (gaussAbs q g) ≤ Real.log ((1 : Submodule (𝓞 F) F).toAddSubgroup.relIndex I.toAddSubgroup) + ∑ᶠ q : FinitePlace F, Real.log (q δ) := by
  first | exact @GlobalTheory.GaussFrac.finsum_log_gaussAbs_le | exact GlobalTheory.GaussFrac.finsum_log_gaussAbs_le | (intros; apply GlobalTheory.GaussFrac.finsum_log_gaussAbs_le <;> assumption)
