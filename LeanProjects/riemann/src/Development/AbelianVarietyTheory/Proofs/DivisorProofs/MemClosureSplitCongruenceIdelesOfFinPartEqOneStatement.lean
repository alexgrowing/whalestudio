import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemClosureSplitCongruenceIdelesOfFinPartEqOne
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitLocF
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_closure_split_congruence_ideles_of_finPart_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (N : ℕ), 0 < N → ∀ z : (AF F ⊗[F] E)ˣ, finPartF F E (z : AF F ⊗[F] E) = 1 → z ∈ closure (GlobalTheory.HeckeSplitGen.grpHF σ N : Set (AF F ⊗[F] E)ˣ) := by
  first | exact @GlobalTheory.HeckeSplitGen.mem_closure_grpHF_of_finPart_eq_one | exact GlobalTheory.HeckeSplitGen.mem_closure_grpHF_of_finPart_eq_one | (intros; apply GlobalTheory.HeckeSplitGen.mem_closure_grpHF_of_finPart_eq_one <;> assumption)
