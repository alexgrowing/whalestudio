import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatDegreeDivisorsProdDistinctMonicIrreducible
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabelsCharOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalCharacterFormula
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesLabelExistsUniqueGLn

open Polynomial GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters GlobalTheory.ParamLabel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.natDegree_divisors_prod_distinct_monic_irreducible : ∀ (k : Type) [Field k] (ι : Type) [Fintype ι] (P : ι → k[X]), (∀ c, (P c).Monic ∧ Irreducible (P c)) → Function.Injective P → (∀ a : ℕ, (∃ q : k[X], q ∣ ∏ c, P c ∧ q.natDegree = a) ↔ ∃ A : Finset ι, ∑ c ∈ A, (P c).natDegree = a) ∧ ∀ Q : ℕ → Prop, (∃ q : k[X], Irreducible q ∧ q ∣ ∏ c, P c ∧ Q q.natDegree) ↔ ∃ c, Q (P c).natDegree := by
  first | exact @GlobalTheory.Div.natDegree_divisors_prod_distinct_monic_irreducible.natDegree_divisors_prod | exact GlobalTheory.Div.natDegree_divisors_prod_distinct_monic_irreducible.natDegree_divisors_prod | (intros; apply GlobalTheory.Div.natDegree_divisors_prod_distinct_monic_irreducible.natDegree_divisors_prod <;> assumption)
