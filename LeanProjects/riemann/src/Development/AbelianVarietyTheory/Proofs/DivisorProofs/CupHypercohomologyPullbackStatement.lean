import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupHypercohomologyPullback
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cup_hypercohomologyPullback : ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E E' : Spc} (f : E ⟶ E') {n m k : ℤ} (hk : n + m = k) a b, cpull ((chains R).map f) K k (μ.cup E' hk a b) = μ.cup E hk (cpull ((chains R).map f) I n a) (cpull ((chains R).map f) J m b) := by
  first | (exact @GlobalTheory.EtC.Pair.cup_pull) | (exact GlobalTheory.EtC.Pair.cup_pull) | (intros; apply GlobalTheory.EtC.Pair.cup_pull  <;> assumption)
