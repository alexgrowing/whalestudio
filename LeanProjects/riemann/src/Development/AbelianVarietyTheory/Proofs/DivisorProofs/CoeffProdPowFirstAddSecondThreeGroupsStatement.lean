import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffProdPowFirstAddSecondThreeGroups
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_prod_pow_first_add_second_threeGroups : ∀ {R : Type} [CommRing R] {d : ℕ} (α : Fin d ⊕ Fin d →₀ ℕ) (a b e : Fin d →₀ ℕ), coeff (Finsupp.sumElim a (Finsupp.sumElim b e)) (α.prod fun s k => (Sum.elim (fun i => (x1 i + x2 i : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R)) x3 s) ^ k) = if α = Finsupp.sumElim (a + b) e then (∏ i, ((a + b) i).choose (a i) : R) else 0 := by
  first | exact @GlobalTheory.BinomLeft.coeff_prod_pow_add | exact GlobalTheory.BinomLeft.coeff_prod_pow_add | (intros; apply GlobalTheory.BinomLeft.coeff_prod_pow_add <;> assumption)
