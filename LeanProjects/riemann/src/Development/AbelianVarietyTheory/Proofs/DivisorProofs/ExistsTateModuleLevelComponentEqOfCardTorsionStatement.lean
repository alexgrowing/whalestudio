import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTateModuleLevelComponentEqOfCardTorsion
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
open GlobalTheory.HTLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tateModule_levelComponent_eq_of_card_torsion : ∀ (M : Type) [CommGroup M] (l : ℕ) [Fact l.Prime] (c : ℕ), (∀ k : ℕ, Nat.card {x : M // x ^ (l ^ k) = 1} = l ^ (c * k)) → ∀ (N : ℕ) (x : M), x ^ (l ^ N) = 1 → ∃ t : Tate l M, t.lev N = x := by
  first | exact @GlobalTheory.exists_tate_lev_eq_of_card_torsion | exact GlobalTheory.exists_tate_lev_eq_of_card_torsion | (intros; apply GlobalTheory.exists_tate_lev_eq_of_card_torsion <;> assumption)
