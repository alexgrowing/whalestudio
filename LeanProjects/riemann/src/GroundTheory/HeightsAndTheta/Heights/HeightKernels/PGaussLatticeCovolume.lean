import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGauss
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix MeasureTheory Module

noncomputable section

namespace PGaussLatticeCovolume

def cols {g : ℕ} (B : Matrix (Fin g) (Fin g) ℝ) : Fin g → EuclideanSpace ℝ (Fin g) :=
  fun i => WithLp.toLp 2 (B *ᵥ Pi.single i 1)

theorem cols_linearIndependent {g : ℕ} {B : Matrix (Fin g) (Fin g) ℝ} (hB : B.det ≠ 0) :
    LinearIndependent ℝ (cols B) := by
  have h := Matrix.linearIndependent_cols_of_det_ne_zero hB
  have e : cols B = (WithLp.linearEquiv 2 ℝ (Fin g → ℝ)).symm ∘ B.col := by
    funext i
    simp [cols]
  rw [e]
  exact h.map' _ (LinearEquiv.ker _)

def colBasis {g : ℕ} {B : Matrix (Fin g) (Fin g) ℝ} (hB : B.det ≠ 0) :
    Basis (Fin g) ℝ (EuclideanSpace ℝ (Fin g)) :=
  basisOfLinearIndependentOfCardEqFinrank' (cols B) (cols_linearIndependent hB) (by simp)

theorem coe_colBasis {g : ℕ} {B : Matrix (Fin g) (Fin g) ℝ} (hB : B.det ≠ 0) :
    ⇑(colBasis hB) = cols B := by
  simp [colBasis]

theorem span_colBasis {g : ℕ} {B : Matrix (Fin g) (Fin g) ℝ} (hB : B.det ≠ 0) :
    Submodule.span ℤ (Set.range (colBasis hB)) = gaussLattice B := by
  rw [coe_colBasis]
  rfl

def intBasis {g : ℕ} {B : Matrix (Fin g) (Fin g) ℝ} (hB : B.det ≠ 0) :
    Basis (Fin g) ℤ (gaussLattice B) :=
  ((colBasis hB).restrictScalars ℤ).map (LinearEquiv.ofEq _ _ (span_colBasis hB))

theorem coe_intBasis {g : ℕ} {B : Matrix (Fin g) (Fin g) ℝ} (hB : B.det ≠ 0) :
    ((↑) : gaussLattice B → EuclideanSpace ℝ (Fin g)) ∘ intBasis hB = cols B := by
  funext i
  simp [intBasis, Basis.restrictScalars_apply, coe_colBasis]

theorem det_cols {g : ℕ} (B : Matrix (Fin g) (Fin g) ℝ) :
    (EuclideanSpace.basisFun (Fin g) ℝ).toBasis.det (cols B) = B.det := by
  rw [Basis.det_apply]
  congr 1
  ext i j
  simp [Basis.toMatrix_apply, cols]

theorem volume_fundamentalDomain_basisFun (g : ℕ) :
    volume.real (ZSpan.fundamentalDomain (EuclideanSpace.basisFun (Fin g) ℝ).toBasis) = 1 := by
  rw [measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped _ volume),
    OrthonormalBasis.coe_toBasis, measureReal_def,
    (EuclideanSpace.basisFun (Fin g) ℝ).volume_parallelepiped, ENNReal.toReal_one]

end PGaussLatticeCovolume

open PGaussLatticeCovolume in

theorem GaussLatticeCovolume.proof (hL : GaussLatticeIsLattice.Statement) :
    GaussLatticeCovolume.Statement := by
  intro g B hB
  have : DiscreteTopology (gaussLattice B) := (hL g B hB).1
  have : IsZLattice ℝ (gaussLattice B) := (hL g B hB).2
  rw [ZLattice.covolume_eq_det_mul_measureReal (gaussLattice B) volume (intBasis hB)
      (EuclideanSpace.basisFun (Fin g) ℝ).toBasis,
    coe_intBasis, det_cols, volume_fundamentalDomain_basisFun, mul_one]

end

end GroundTheory.Heights₂.Heights
