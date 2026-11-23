import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetRingProdEqZeroOfLong
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
open GlobalTheory.LatJet
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jet_ring_prod_eq_zero_of_long : ∀ {R : Type} [CommRing R] {I : Type} [Fintype I] {n : ℕ} (J : JetRing R I n) (l : List I), n + 1 < l.length → (l.map J.t).prod = 0 := by
  first | exact @GlobalTheory.LatJet.ProdZero.prod_eq_zero | exact GlobalTheory.LatJet.ProdZero.prod_eq_zero | (intros; apply GlobalTheory.LatJet.ProdZero.prod_eq_zero <;> assumption)
