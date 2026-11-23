import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralMatrixOfMapsToFullRankLattice
import Mathlib
import Formalism.SatakeDualWeyl.Statement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMatLat
open Polynomial Matrix GlobalTheory.LatOrb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_matrix_of_mapsTo_fullRankLattice : ∀ {O K : Type} [CommRing O] [Field K] [Algebra O K] (n : ℕ) (M : Submodule O (Fin n → K)),
    IsLatV O M → ∀ c : Matrix (Fin n) (Fin n) K, (∀ v ∈ M, c *ᵥ v ∈ M) → IsIntegral O c := by
  first | exact @GlobalTheory.LatOrb.isIntegral_of_mapsTo_lattice | exact GlobalTheory.LatOrb.isIntegral_of_mapsTo_lattice | (intros; apply GlobalTheory.LatOrb.isIntegral_of_mapsTo_lattice <;> assumption)
