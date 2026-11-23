import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.StdCharIffInt

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

namespace GlobalTheory.DualPairCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}
section Gen
variable {R : Type} [CommRing R] {a b : ℕ}

def thenTr (φ : Matrix (Fin a) (Fin b) R ≃ₗ[R] Matrix (Fin a) (Fin b) R) :
    Matrix (Fin a) (Fin b) R ≃ₗ[R] Matrix (Fin b) (Fin a) R :=
  φ.trans (Matrix.transposeLinearEquiv _ _ R R)

theorem leftMul_apply (J Ji : Matrix (Fin a) (Fin a) R) (h1 : Ji * J = 1) (x : Matrix (Fin a) (Fin b) R) :
    leftMul J Ji h1 x = Jiᵀ * x := rfl

end Gen

open GlobalTheory.IndefiniteRowSideFullHecke

instance topRing (D : D7) : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _

theorem gramInv_mul (A : HSp D) : HeisenbergWeilMatrices.gramInvA A * HeisenbergWeilMatrices.gramA A = 1 := by
  unfold HeisenbergWeilMatrices.gramInvA HeisenbergWeilMatrices.gramA
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (gram_det_ne A))]
  exact Matrix.map_one _ (incA D).map_zero (incA D).map_one

def coordUp (A B : HSp D) : HeisenbergWeilMatrices.WA A B ≃ₗ[AE D] WA A B :=
  leftMul (HeisenbergWeilMatrices.gramA A) (HeisenbergWeilMatrices.gramInvA A) (gramInv_mul A)

def coordDn (V W : HSp D) : HeisenbergWeilMatrices.WA W V ≃ₗ[AE D] WA V W :=
  thenTr (coordUp W V)

theorem coordUp_eq (A B : HSp D) (x : HeisenbergWeilMatrices.WA A B) : coordUp A B x = HMul.hMul (HeisenbergWeilMatrices.gramInvA A)ᵀ x :=
  leftMul_apply _ _ (gramInv_mul A) x

theorem cont_up (A B : HSp D) : Continuous (coordUp A B) ∧ Continuous (coordUp A B).symm :=
  gen_cont _ _ (gramInv_mul A)

structure IsCoord {V W A B : HSp D} (φ : HeisenbergWeilMatrices.WA A B ≃ₗ[AE D] WA V W) : Prop where
  cont : Continuous φ
  cont_symm : Continuous φ.symm
  herm : ∀ x y, hHom V W (φ y) (φ x) = HeisenbergWeilMatrices.herm x y
  rat : ∀ x, φ x ∈ ratL V W ↔ x ∈ HeisenbergWeilMatrices.WQ A B
  inf : ∀ x, (φ x).map (infPart D) = 0 ↔ x.map (infPart D) = 0
  fin : ∀ x, (φ x).map (finPart D) = 0 ↔ x.map (finPart D) = 0

end GlobalTheory.DualPairCompare

end
