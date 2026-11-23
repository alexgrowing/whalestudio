import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteOfResidueFiniteComplete
import Mathlib
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_of_residue_finite_complete : ∀ {B R : Type} [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [CommRing R] [IsLocalRing R] (ψ : B →+* R), IsAdicComplete (maximalIdeal B) B → IsAdicComplete (maximalIdeal R) R → (maximalIdeal B).map ψ = maximalIdeal R → ((residue R).comp ψ).Finite → ψ.Finite := by
  first | exact @GlobalTheory.CompleteNakayamaLocal.finite_of_maximalIdeal_map_eq | exact GlobalTheory.CompleteNakayamaLocal.finite_of_maximalIdeal_map_eq | (intros; apply GlobalTheory.CompleteNakayamaLocal.finite_of_maximalIdeal_map_eq <;> assumption)
