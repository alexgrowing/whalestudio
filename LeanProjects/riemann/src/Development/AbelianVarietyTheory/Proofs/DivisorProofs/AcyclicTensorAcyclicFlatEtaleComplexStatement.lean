import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AcyclicTensorAcyclicFlatEtaleComplex
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.acyclic_tensor_acyclic_flatEtaleComplex : ∀ (R : Type) [CommRing R] {C J T : Cx R} (a b : ℤ) [C.IsStrictlyGE a] [J.IsStrictlyGE b] (τ : Pair C J T), τ.IsTensor → (∀ t, FlatS (J.X t)) → C.Acyclic → T.Acyclic := by
  first | (exact @GlobalTheory.EtC.acyclic_of_isTensor) | (exact GlobalTheory.EtC.acyclic_of_isTensor) | (intros; apply GlobalTheory.EtC.acyclic_of_isTensor  <;> assumption)
