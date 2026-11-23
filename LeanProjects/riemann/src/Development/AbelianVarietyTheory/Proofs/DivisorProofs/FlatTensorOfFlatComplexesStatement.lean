import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatTensorOfFlatComplexes
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_tensor_of_flat_complexes : ∀ (R : Type) [CommRing R] {I J T : Cx R} (τ : Pair I J T), τ.IsTensor → (∀ t, FlatS (I.X t)) → (∀ t, FlatS (J.X t)) → ∀ w, FlatS (T.X w) := by
  first | (exact @GlobalTheory.EtC.FlatTens.flatS_tens) | (exact GlobalTheory.EtC.FlatTens.flatS_tens) | (intros; apply GlobalTheory.EtC.FlatTens.flatS_tens  <;> assumption)
