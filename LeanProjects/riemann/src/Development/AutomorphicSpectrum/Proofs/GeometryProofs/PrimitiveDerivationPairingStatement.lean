import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimitiveDerivationPairing
import Mathlib
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitive_derivation_pairing : ∀ (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (A : Type) [CommRing A] [HopfAlgebra k A] [Coalgebra.IsCocomm k A] [Module.Finite k A]
    (P : Submodule k A) (W : Submodule k (A →ₗ[k] k)),
    (∀ f ∈ P, Coalgebra.comul (R := k) f = f ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] f) →
    (∀ v ∈ W, ∀ f g : A, v (f * g) = v f * Coalgebra.counit (R := k) g + Coalgebra.counit (R := k) f * v g) →
    (∀ v ∈ W, ∀ f ∈ P, v f = 0) →
    p ^ (Module.finrank k P + Module.finrank k W) ∣ Module.finrank k A := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HopfCount.primitive_tangent_dvd_finrank | exact GlobalTheory.CompanionTheory.Ar.HopfCount.primitive_tangent_dvd_finrank | (intros; apply GlobalTheory.CompanionTheory.Ar.HopfCount.primitive_tangent_dvd_finrank <;> assumption)
