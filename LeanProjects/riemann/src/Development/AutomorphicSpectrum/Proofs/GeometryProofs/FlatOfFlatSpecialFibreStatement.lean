import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatOfFlatSpecialFibre
import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ModuleFlatOfFlatAndFibreFlatStatement
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_of_flat_special_fibre : ∀ (R P Q : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing P] [CommRing Q] [Algebra R P] [Algebra R Q] [Module.Finite R P] [Module.Finite R Q] [Module.Flat R Q] (φ : P →ₐ[R] Q), (Algebra.TensorProduct.map (AlgHom.id R (IsLocalRing.ResidueField R)) φ).toRingHom.Flat → φ.toRingHom.Flat := by
  first | exact @GlobalTheory.CompanionTheory.FinAlgFlat.ringHom_flat_of_fibre_flat | exact GlobalTheory.CompanionTheory.FinAlgFlat.ringHom_flat_of_fibre_flat | (intros; apply GlobalTheory.CompanionTheory.FinAlgFlat.ringHom_flat_of_fibre_flat <;> assumption)
