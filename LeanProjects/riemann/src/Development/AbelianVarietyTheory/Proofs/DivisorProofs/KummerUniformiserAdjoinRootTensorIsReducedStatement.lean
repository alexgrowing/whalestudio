import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerUniformiserAdjoinRootTensorIsReduced
import Mathlib
open IsLocalRing
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummer_uniformiser_adjoinRoot_tensor_isReduced : ∀ (S K L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Algebra S K] [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L] [IsScalarTower S K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (π : S) (e : ℕ) (D : Type) [CommRing D] [Algebra S D],
    Nonempty (D ≃ₐ[S] AdjoinRoot (Polynomial.X ^ e - Polynomial.C π)) → Irreducible π → IsUnit (e : S) →
    IsReduced (TensorProduct S D L) := by
  first | (exact @GlobalTheory.kummer_uniformiser_tensor_isReduced) | (exact GlobalTheory.kummer_uniformiser_tensor_isReduced) | (intros; apply GlobalTheory.kummer_uniformiser_tensor_isReduced  <;> assumption)
