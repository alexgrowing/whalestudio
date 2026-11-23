import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsOrthogonalHermitianSubspace
import Mathlib
import Formalism.RealPlaceAnalysis.SmoothOnGVIff
import Formalism.FormalDegreeBessel.StatementG
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.involution_stable_subspace_coordinate : ∀ {n : ℕ} (ε : Fin n → Bool) (W : Submodule ℂ (Fin n → ℂ)), (∀ v ∈ W, Formalism.REAL.Jm ε *ᵥ v ∈ W) →
    ∃ (k : Formalism.REAL.KG ε) (S : Set (Fin n)),
      W = (Submodule.span ℂ (Set.range fun j : S => (Pi.single (j : Fin n) (1 : ℂ) : Fin n → ℂ))).map (Formalism.REAL.toMK k).mulVecLin := by
  first | exact @GlobalTheory.CompanionTheory.JStable.exists_KG_coordinate | exact GlobalTheory.CompanionTheory.JStable.exists_KG_coordinate | (intros; apply GlobalTheory.CompanionTheory.JStable.exists_KG_coordinate <;> assumption)
