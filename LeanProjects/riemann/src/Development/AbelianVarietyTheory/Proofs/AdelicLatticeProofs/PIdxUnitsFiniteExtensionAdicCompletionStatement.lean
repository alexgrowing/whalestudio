import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PIdxUnitsFiniteExtensionAdicCompletion
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pIdx_units_finite_extension_adicCompletion' : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (e : ℕ) (L : Type) [Field L] [Algebra (v.adicCompletion F) L] [FiniteDimensional (v.adicCompletion F) L], 0 < p → v.valuation F (p : F) = WithZero.exp (-(e : ℤ)) → pTor p (⊤ : Subgroup Lˣ) ≠ 0 ∧ pIdx p (⊤ : Subgroup Lˣ) = p * (Ideal.absNorm v.asIdeal ^ e) ^ Module.finrank (v.adicCompletion F) L * pTor p (⊤ : Subgroup Lˣ) := by
  first | exact @GlobalTheory.CNorm.pIdx_units_finite_extension_adicCompletion | exact GlobalTheory.CNorm.pIdx_units_finite_extension_adicCompletion | (intros; apply GlobalTheory.CNorm.pIdx_units_finite_extension_adicCompletion <;> assumption)
