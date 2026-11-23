import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCommonIndexIdealInfSupLattices
import Formalism.LocalToGlobal.ProjectiveLattices.ThClass
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIndexIdeal
open NumberField IsDedekindDomain Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_indexIdeal_inf_sup_lattices : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (M M' : Submodule (𝓞 E) (Fin n → E)), GlobalTheory.BetaEx.Bdd (M' ⊔ M) → (∀ m ∈ M, ∃ a : 𝓞 E, a ≠ 0 ∧ a • m ∈ M') → ∃ 𝔞 : Ideal (𝓞 E), 𝔞 ≠ ⊥ ∧ GlobalTheory.BetaEx.detSpan (M ⊓ M') = 𝔞 • GlobalTheory.BetaEx.detSpan M ∧ GlobalTheory.BetaEx.detSpan M' = 𝔞 • GlobalTheory.BetaEx.detSpan (M' ⊔ M) ∧ Ideal.absNorm 𝔞 = (M ⊓ M').toAddSubgroup.relIndex M.toAddSubgroup := by
  first | exact @GlobalTheory.BetaEx.exists_index_ideal_inf_sup | exact GlobalTheory.BetaEx.exists_index_ideal_inf_sup | (intros; apply GlobalTheory.BetaEx.exists_index_ideal_inf_sup <;> assumption)
