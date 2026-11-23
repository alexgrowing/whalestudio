import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPosNatSmulMemOfFgAndSpanningLattice
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
open NumberField ReciprocityTheory.ChartRestriction.G.FD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pos_nat_smul_mem_of_fg_and_spanning_lattice : ∀ {E : Type} [Field E] [NumberField E] {r : ℕ} (Λ Λ' : Submodule (𝓞 E) (Fin r → E)), Λ'.FG → Submodule.span E (Λ : Set (Fin r → E)) = ⊤ → ∃ n : ℕ, 0 < n ∧ ∀ v ∈ Λ', (n : E) • v ∈ Λ := by
  first | exact @GlobalTheory.exists_pos_nat_smul_mem_of_fg_of_span_eq_top | exact GlobalTheory.exists_pos_nat_smul_mem_of_fg_of_span_eq_top | (intros; apply GlobalTheory.exists_pos_nat_smul_mem_of_fg_of_span_eq_top <;> assumption)
