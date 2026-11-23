import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetRingProdEqFactorialSmul
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
open GlobalTheory.LatJet
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jet_ring_prod_eq_factorial_smul : ∀ {R : Type} [CommRing R] {I : Type} [Fintype I] {n : ℕ} (J : JetRing R I n) (l : List I) (hc : ∑ i, l.count i ≤ n + 1), (l.map J.t).prod = ((∏ i, (l.count i).factorial : ℕ) : R) • J.b ⟨fun i => l.count i, hc⟩ := by
  first | exact @GlobalTheory.LatJet.prod_map_t_eq_smul_b | exact GlobalTheory.LatJet.prod_map_t_eq_smul_b | (intros; apply GlobalTheory.LatJet.prod_map_t_eq_smul_b <;> assumption)
