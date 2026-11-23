import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffProdPowSecondAddThirdThreeGroups
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_prod_pow_x1_x2_add_x3 : ∀ {R : Type} [CommRing R] {d : ℕ} (α : Fin d ⊕ Fin d →₀ ℕ) (a b e : Fin d →₀ ℕ), coeff (Finsupp.sumElim a (Finsupp.sumElim b e)) (α.prod fun s k => (Sum.elim x1 (fun i => (x2 i + x3 i : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R)) s) ^ k) = if α = Finsupp.sumElim a (b + e) then (∏ i, ((b + e) i).choose (b i) : R) else 0 := by
  first | exact @GlobalTheory.BinomRight.coeff_prod_pow_second_add_third_threeGroups | exact GlobalTheory.BinomRight.coeff_prod_pow_second_add_third_threeGroups | (intros; apply GlobalTheory.BinomRight.coeff_prod_pow_second_add_third_threeGroups <;> assumption)
