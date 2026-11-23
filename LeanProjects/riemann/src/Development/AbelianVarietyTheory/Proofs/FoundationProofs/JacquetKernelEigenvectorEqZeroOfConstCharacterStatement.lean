import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JacquetKernelEigenvectorEqZeroOfConstCharacter
import Development.AbelianVarietyTheory.Definitions.Foundations.OrderedConst
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquetKernel_eigenvector_eq_zero_of_const_character : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (χ : kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → IsSmoothChar χ → ∀ v ∈ twKer π (unipB k (Fin n)) 1, IsEig π (grp fun _ => χ) (theta fun _ => χ) v → v = 0 := by
  first | exact @GlobalTheory.PsType.eq_zero_of_isEig_const | exact GlobalTheory.PsType.eq_zero_of_isEig_const | (intros; apply GlobalTheory.PsType.eq_zero_of_isEig_const <;> assumption)
