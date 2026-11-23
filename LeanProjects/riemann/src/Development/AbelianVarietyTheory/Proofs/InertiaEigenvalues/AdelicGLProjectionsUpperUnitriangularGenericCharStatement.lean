import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLProjectionsUpperUnitriangularGenericChar
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIdempotentElemIdemSf
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicGLProjections_upperUnitriangular_genericChar : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))), ∀ u ∈ GlobalTheory.JSW.NA E a, prS S a u ∈ GlobalTheory.JSW.NA E a ∧ prO S a u ∈ GlobalTheory.JSW.NA E a ∧ GlobalTheory.JSW.psiN (prS S a u) * GlobalTheory.JSW.psiN (prO S a u) = GlobalTheory.JSW.psiN u := by
  first | (exact @GlobalTheory.SchurExt.prS_prO_NA_psiN) | (exact GlobalTheory.SchurExt.prS_prO_NA_psiN) | (intros; apply GlobalTheory.SchurExt.prS_prO_NA_psiN  <;> assumption)
