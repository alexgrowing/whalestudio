import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VoganNormSqHolomorphicLowestKTypeSubRootLt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.voganNormSq_holomorphicLowestKType_sub_root_lt : ∀ (n p : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → (∀ a, ε a = decide ((a : ℕ) < p)) → ∀ a c : Fin n, ε a = true → ε c = false → vNormSq ε (Formalism.QuantumDeterminants.lowK ε lam - Formalism.REAL.root a c) < vNormSq ε (Formalism.QuantumDeterminants.lowK ε lam) := by
  first | exact @GlobalTheory.HolDict.vNormSq_lowK_sub_noncompact_root_lt | exact GlobalTheory.HolDict.vNormSq_lowK_sub_noncompact_root_lt | (intros; apply GlobalTheory.HolDict.vNormSq_lowK_sub_noncompact_root_lt <;> assumption)
