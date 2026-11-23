import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankIInfKerEqOfIsBaseChangeFamily
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_iInf_ker_eq_of_isBaseChange_family : ∀ (K L V W ι : Type) [Field K] [Field L] [Algebra K L] [Finite ι] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [AddCommGroup W] [Module K W] [Module L W] [IsScalarTower K L W] (f : V →ₗ[K] W), IsBaseChange L f → ∀ (a : ι → V →ₗ[K] V) (a' : ι → W →ₗ[L] W), (∀ i v, a' i (f v) = f (a i v)) → finrank L (⨅ i, LinearMap.ker (a' i) : Submodule L W) = finrank K (⨅ i, LinearMap.ker (a i) : Submodule K V) ∧ (⨅ i, LinearMap.ker (a' i) : Submodule L W) = Submodule.span L (f '' ((⨅ i, LinearMap.ker (a i) : Submodule K V) : Set V)) := by
  first | exact @GlobalTheory.BadCount.finrank_iInf_ker_baseChange | exact GlobalTheory.BadCount.finrank_iInf_ker_baseChange | (intros; apply GlobalTheory.BadCount.finrank_iInf_ker_baseChange <;> assumption)
