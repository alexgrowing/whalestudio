import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArithFrobeniusEmbeddingPermCmConj
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
open NumberField IsDedekindDomain GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization Formalism.L2.Host GlobalTheory.HeckeGal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_arithFrobenius_embedding_perm_cmConj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime], ¬ (l : ℤ) ∣ NumberField.discr E → ∃ σ : Equiv.Perm (E →+* PadicAlgCl l), IsFrobPerm σ ∧ ∀ τ, σ (cj τ) = cj (σ τ) := by
  first | exact @GlobalTheory.FrobEmb.exists_frobPerm | exact GlobalTheory.FrobEmb.exists_frobPerm | (intros; apply GlobalTheory.FrobEmb.exists_frobPerm <;> assumption)
