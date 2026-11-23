import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransportMatrixIdentityInjectiveRingHom
import Mathlib
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transport_matrix_identity_injective_ringHom : ∀ {R L : Type} [CommRing R] [CommRing L] (ι : R →+* L), Function.Injective ι → ∀ (d N q : ℕ) (p : Fin d → ℕ) (ξ s : R) (Qm Q₁ : Matrix (Fin d) (Fin d) L) (X B c V : Matrix (Fin d) (Fin d) R), ι s ^ N • Qm = (X * B).map ι → (∀ i j, ι ξ ^ q * Q₁ i j = ι (ξ ^ p j * V i j)) → Q₁ = Qm * c.map ι → ξ ^ q • (X * B * c) = s ^ N • (V * Matrix.diagonal (fun j => ξ ^ p j)) := by
  first | (exact @GlobalTheory.transport_matrix_identity_star_alg) | (exact GlobalTheory.transport_matrix_identity_star_alg) | (intros; apply GlobalTheory.transport_matrix_identity_star_alg  <;> assumption)
