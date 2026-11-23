import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdEndomorphismPowLevelComponentEqOneOfRelation
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
open GlobalTheory.HTLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_endomorphism_pow_levelComponent_eq_one_of_relation : ∀ (M : Type) [CommGroup M] (l : ℕ) [Fact l.Prime] (n : ℕ) (φ : Fin n → (M →* M)) (c : Fin n → ℤ_[l]), ∑ i, c i • Tate.map l (φ i) = 0 → ∀ (N : ℕ) (m : Fin n → ℤ), (∀ i, PadicInt.toZModPow N (c i) = (m i : ZMod (l ^ N))) → ∀ t : Tate l M, ∏ i, φ i (t.lev N) ^ m i = 1 := by
  first | exact @GlobalTheory.TateRel.prod_pow_eq_one | exact GlobalTheory.TateRel.prod_pow_eq_one | (intros; apply GlobalTheory.TateRel.prod_pow_eq_one <;> assumption)
