import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixImageAdjointMulEqOfSelfDualLattices
import Mathlib
import Formalism.SatakeDualWeyl.Statement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMatLat
open Polynomial Matrix GlobalTheory.LatOrb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrixImage_adjoint_mul_eq_of_selfDual_lattices : ∀ {O K : Type} [CommRing O] [Field K] [Algebra O K] (σ : K →+* K),
    (∀ x, σ (σ x) = x) → ∀ (n : ℕ) (x : Matrix (Fin n) (Fin n) K), IsUnit x →
    ∀ M : Submodule O (Fin n → K), SelfDual O σ M → SelfDual O σ (matLat O x M) →
    matLat O ((x.map σ)ᵀ * x) M = M := by
  first | exact @GlobalTheory.LatOrb.matLat_adj_mul_eq_of_selfDual | exact GlobalTheory.LatOrb.matLat_adj_mul_eq_of_selfDual | (intros; apply GlobalTheory.LatOrb.matLat_adj_mul_eq_of_selfDual <;> assumption)
