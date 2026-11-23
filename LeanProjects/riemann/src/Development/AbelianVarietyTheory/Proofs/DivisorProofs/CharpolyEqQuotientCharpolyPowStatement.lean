import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyEqQuotientCharpolyPow
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TensorProductAction
open scoped TensorProduct nonZeroDivisors
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charpoly_eq_quotient_charpoly_pow : ∀ (K : Type) [Field K] (X : Type) [AddCommGroup X] [Module K X] [FiniteDimensional K X]
    (t T : Module.End K X) (_ : Commute t T) (e : ℕ) (_ : 0 < e) (_ : t ^ e = 0)
    (_ : ∀ x, t x = 0 → x ∈ LinearMap.range (t ^ (e - 1)))
    (hT : LinearMap.range t ≤ (LinearMap.range t).comap T),
    LinearMap.charpoly T = (LinearMap.charpoly ((LinearMap.range t).mapQ (LinearMap.range t) T hT)) ^ e := by
  first | exact @GlobalTheory.NilpFiltration.charpoly_eq_charpoly_mapQ_pow | exact GlobalTheory.NilpFiltration.charpoly_eq_charpoly_mapQ_pow | (intros; apply GlobalTheory.NilpFiltration.charpoly_eq_charpoly_mapQ_pow <;> assumption)
