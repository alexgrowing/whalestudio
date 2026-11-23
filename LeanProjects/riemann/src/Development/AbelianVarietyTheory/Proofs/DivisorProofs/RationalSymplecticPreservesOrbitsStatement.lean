import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSymplecticPreservesOrbits
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_symplectic_preserves_orbits : ∀ g : ℕ, ∀ γ : Sp g, (∀ i k, ∃ r : ℚ, γ.mat i k = r) → ∀ M : Submodule ℤ (Fl g), IsRatLat M → IsRatLat (latAct M γ) ∧ ∀ P ∈ cov (siegel g) g, ∀ Q ∈ cov (siegel g) g, SameOrbit tauU M P Q ↔ SameOrbit tauU (latAct M γ) (actU γ P) (actU γ Q) := by
  first | exact @GlobalTheory.SymplecticOrbit.sameOrbit_actU_iff | exact GlobalTheory.SymplecticOrbit.sameOrbit_actU_iff | (intros; apply GlobalTheory.SymplecticOrbit.sameOrbit_actU_iff <;> assumption)
