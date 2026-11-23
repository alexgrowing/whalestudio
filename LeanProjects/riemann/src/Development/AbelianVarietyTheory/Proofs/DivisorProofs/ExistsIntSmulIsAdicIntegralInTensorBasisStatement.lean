import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntSmulIsAdicIntegralInTensorBasis
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntBTmulBasis
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_int_smul_isAdicIntegralInTensorBasis : ∀ (M : Type) [AddCommGroup M] [Module ℚ M] (κ : Type) (b : Module.Basis κ ℚ M)
    (v : HeightOneSpectrum ℤ) (y : v.adicCompletion ℚ ⊗[ℚ] M), ∃ D : ℤ, D ≠ 0 ∧ IsIntB v b (D • y) := by
  first | (exact @GlobalTheory.AdicSpan.exists_int_smul_isIntB) | (exact GlobalTheory.AdicSpan.exists_int_smul_isIntB) | (intros; apply GlobalTheory.AdicSpan.exists_int_smul_isIntB  <;> assumption)
