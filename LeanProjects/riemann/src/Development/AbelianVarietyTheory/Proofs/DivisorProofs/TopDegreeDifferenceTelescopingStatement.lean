import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDegreeDifferenceTelescoping
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant
open GlobalTheory.Mean4O
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.top_degree_difference_telescoping : ∀ {e : ℕ} (M : Man e) (K : Calc M) (v : K.V) (φ φ' : M.Fun), M.Smooth φ → M.Smooth φ' → K.top (v + K.ar φ) - K.top (v + K.ar φ') = ∑ i ∈ Finset.range (e + 1), M.int (fun k : Fin e => K.c1 (if (k : ℕ) < i then v + K.ar φ else v + K.ar φ')) (φ - φ') := by
  first | exact @GlobalTheory.Mean4O.Calc.top_add_ar_sub | exact GlobalTheory.Mean4O.Calc.top_add_ar_sub | (intros; apply GlobalTheory.Mean4O.Calc.top_add_ar_sub <;> assumption)
