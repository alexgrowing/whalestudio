import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorFlatComplexPreservesQuasiIso
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_flat_complex_preserves_quasiIso : ∀ (R : Type) [CommRing R] {I I' J T T' : Cx R} [I.IsStrictlyGE 0] [I'.IsStrictlyGE 0] [J.IsStrictlyGE 0] (τ : Pair I J T) (τ' : Pair I' J T'), τ.IsTensor → τ'.IsTensor → (∀ t, FlatS (J.X t)) → ∀ (f : I ⟶ I') [QuasiIso f] (u : T ⟶ T'), τ.Compat τ' f (𝟙 J) u → QuasiIso u := by
  first | (exact @GlobalTheory.EtC.tensor_quasiIso) | (exact GlobalTheory.EtC.tensor_quasiIso) | (intros; apply GlobalTheory.EtC.tensor_quasiIso  <;> assumption)
