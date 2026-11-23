import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSHSFG
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LowVLift
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CoordinateSizesOfHypotheses
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyZeroNear

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSH.SFG

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.PBH

theorem radial_embedding_mem_unitary_group {k ρ m : ℕ} (e : ρ + 1 = m) (x : U.RC k 1 ρ) : rn1 e x ∈ B.GV k m := by
  exact PBE.castM_GV e (PBE.castM_GV _ (Ux6.Rn_mem x))

private theorem mMap_mem_GV_of_isUnit_det_of_mem_GV {k j ρ : ℕ} (Z : Matrix (Fin j) (Fin j) ℂ) (hZ : IsUnit Z.det)
    (γ : B.Mat k ρ) (hγ : γ ∈ B.GV k ρ) : U.mMap k j ρ Z γ ∈ B.GV k (j + ρ) := by
  have hr : ∀ a b : Fin j, a = b.rev ↔ b = a.rev := fun a b =>
    ⟨fun h => by rw [h, Fin.rev_rev], fun h => by rw [h, Fin.rev_rev]⟩
  have hw : G.wMat j * G.wMat j = 1 := by
    ext a b
    simp only [G.wMat, Matrix.mul_apply, Matrix.one_apply, Matrix.of_apply]
    rw [Finset.sum_eq_single b.rev]
    · simp [Fin.rev_rev, Fin.rev_inj, eq_comm]
    · intro c _ hc
      rw [if_neg (fun h => hc ((hr c b).2 h))]
      simp
    · simp
  have hwh : (G.wMat j).conjTranspose = G.wMat j := by
    ext a b
    simp only [G.wMat, Matrix.conjTranspose_apply, Matrix.of_apply]
    split_ifs with h1 h2 h2 <;> simp_all [hr]
  have hZ' : IsUnit Z.conjTranspose.det := by
    rw [Matrix.det_conjTranspose]
    exact hZ.star
  have hγ' : Matrix.conjTranspose γ * Hpk k ρ * γ = Hpk k ρ := hγ
  have h1 : Z.conjTranspose * (G.wMat j).conjTranspose * G.wMat j * (Z.conjTranspose⁻¹ * G.wMat j)
      = G.wMat j := by
    rw [hwh, Matrix.mul_assoc Z.conjTranspose, hw, Matrix.mul_one, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hZ', Matrix.one_mul]
  have h3 : (G.wMat j).conjTranspose * Z.conjTranspose⁻¹.conjTranspose * G.wMat j * (G.wMat j * Z)
      = G.wMat j := by
    rw [hwh, Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc, ← Matrix.mul_assoc (G.wMat j) (G.wMat j) Z, hw, Matrix.one_mul,
      Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hZ, Matrix.mul_one]
  show Matrix.conjTranspose (U.mMap k j ρ Z γ) * Hpk k (j + ρ) * U.mMap k j ρ Z γ = Hpk k (j + ρ)
  rw [Ux6.hpkBlocks k j ρ]
  unfold U.mMap
  rw [Ux6.block3_conjTranspose, Ux6.block3_mul, Ux6.block3_mul]
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.conjTranspose_zero,
    Matrix.conjTranspose_mul]
  rw [h1, hγ', h3]

theorem mc_GV {k ρ m : ℕ} (e : ρ + 1 = m) {t : ℂ} (ht : t ≠ 0) {γ : B.Mat k ρ} (hγ : γ ∈ B.GV k ρ) :
    mc e t γ ∈ B.GV k m := by
  unfold mc
  refine PBE.castM_GV e (PBE.castM_GV _ (mMap_mem_GV_of_isUnit_det_of_mem_GV _ ?_ γ hγ))
  simp [Matrix.det_unique, ht]

theorem point_mem_unitary_group : PtGV := by
  intro k ρ m e t ht γ hγ xx
  unfold pt
  exact HermitianFormFactor.UH_mul (HermitianFormFactor.UH_mul (HermitianFormFactor.UH_inv (B2x5.isUnit_det_Hpk k m) (radial_embedding_mem_unitary_group e xx.1))
    (mc_GV e ht hγ)) (radial_embedding_mem_unitary_group e xx.2)

end Formalism.FourierDecayAlt.P.CutSH.SFG
