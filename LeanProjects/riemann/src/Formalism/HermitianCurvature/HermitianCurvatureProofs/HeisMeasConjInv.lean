import Formalism.HermitianCurvature.HermitianCurvatureProofs.UwClosedSubgroup
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LongWeylElement
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeisenbergLeviConjugationMeasure
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentHeisenbergDecomposition

open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

variable {k : ℕ}

private theorem iotaLev_one_eq_blk3 (ρ : ℕ) (g : B.Mat k ρ) :
    ιLev k 1 ρ g = U.blk3 (j := 1) 1 0 0 0 g 0 0 0 1 := by
  ext p q
  obtain ⟨x, rfl⟩ := (U.eB k 1 ρ).surjective p
  obtain ⟨y, rfl⟩ := (U.eB k 1 ρ).surjective q
  rw [Ux3.block3_apply]
  have vX : ∀ x : Fin 1, ((U.eB k 1 ρ) (Sum.inl (Sum.inl x))).val = 0 := fun x => by
    simp [U.eB]
  have vV : ∀ v : Fin (2 * ρ + k + 1), ((U.eB k 1 ρ) (Sum.inl (Sum.inr v))).val = 1 + v.val := fun v => by
    simp [U.eB]
  have vS : ∀ b : Fin 1, ((U.eB k 1 ρ) (Sum.inr b)).val = 2 * ρ + k + 2 := fun b => by
    simp [U.eB] <;> omega
  rcases x with (x | x) | x <;> rcases y with (y | y) | y <;>
    simp only [Formalism.QuantumDeterminants.ιLev, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl,
      Matrix.fromCols_apply_inr, Matrix.zero_apply, Matrix.one_apply, vX, vV, vS, Equiv.apply_eq_iff_eq,
      Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] <;>
    split_ifs <;> first | rfl | (exfalso; omega) | (congr <;> (try apply Fin.ext) <;> simp [vV])

theorem lev_mMap (ρ : ℕ) (g g' : B.Mat k ρ) (Z : Matrix (Fin 1) (Fin 1) ℂ) (γ : B.Mat k ρ) :
    ιLev k 1 ρ g * U.mMap k 1 ρ Z γ * ιLev k 1 ρ g' = U.mMap k 1 ρ Z (g * γ * g') := by
  rw [iotaLev_one_eq_blk3, iotaLev_one_eq_blk3]
  simp only [U.mMap]
  rw [Ux5.block3_mul_blocks, Ux5.block3_mul_blocks]
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, add_zero, zero_add]

theorem sgs_alg (ρ : ℕ) (h0 y h0' y' : B.Mat k ρ) (hh0 : IsUnit h0.det) (hy : IsUnit y.det) (hh0' : IsUnit h0'.det)
    (hy' : IsUnit y'.det) (a a' : B.Mat k (1 + ρ)) (Z : Matrix (Fin 1) (Fin 1) ℂ) (γ : B.Mat k ρ) :
    (ιLev k 1 ρ h0)⁻¹ * (a * ιLev k 1 ρ y)⁻¹ * U.mMap k 1 ρ Z γ * (a' * ιLev k 1 ρ y') * ιLev k 1 ρ h0' =
      ((ιLev k 1 ρ (y * h0))⁻¹ * a * ιLev k 1 ρ (y * h0))⁻¹ *
        U.mMap k 1 ρ Z ((y * h0)⁻¹ * γ * (y' * h0')) * ((ιLev k 1 ρ (y' * h0'))⁻¹ * a' * ιLev k 1 ρ (y' * h0')) := by
  have hL0 := PI.QnLevBasicsW.level_group_homomorphism
  have hL := hL0
  unfold Formalism.QuantumDeterminants.LevHom at hL
  have ιmul : ∀ g h : B.Mat k ρ, ιLev k 1 ρ (g * h) = ιLev k 1 ρ g * ιLev k 1 ρ h := (hL k 1 ρ).2
  have ιone : ιLev k 1 ρ (1 : B.Mat k ρ) = 1 := (hL k 1 ρ).1
  have ιinv : ∀ g : B.Mat k ρ, IsUnit g.det → (ιLev k 1 ρ g)⁻¹ = ιLev k 1 ρ g⁻¹ :=
    fun g hg => PIQnLT.ιLev_inv hL0 g hg
  have hW : IsUnit (y * h0).det := by
    rw [Matrix.det_mul]
    exact hy.mul hh0
  have hW' : IsUnit (y' * h0').det := by
    rw [Matrix.det_mul]
    exact hy'.mul hh0'
  have hW1 : ∀ X, ιLev k 1 ρ (y * h0) * (ιLev k 1 ρ (y * h0)⁻¹ * X) = X := by
    intro X
    rw [← mul_assoc, ← ιmul, Matrix.mul_nonsing_inv _ hW, ιone, one_mul]
  have hW2 : ∀ X, ιLev k 1 ρ (y' * h0') * (ιLev k 1 ρ (y' * h0')⁻¹ * X) = X := by
    intro X
    rw [← mul_assoc, ← ιmul, Matrix.mul_nonsing_inv _ hW', ιone, one_mul]
  have hLw : ∀ X, ιLev k 1 ρ h0⁻¹ * (ιLev k 1 ρ y⁻¹ * X) = ιLev k 1 ρ (y * h0)⁻¹ * X := by
    intro X
    rw [← mul_assoc, ← ιmul, Matrix.mul_inv_rev]
  have hRw : ιLev k 1 ρ y' * ιLev k 1 ρ h0' = ιLev k 1 ρ (y' * h0') := (ιmul _ _).symm
  rw [Matrix.mul_inv_rev a, ιinv _ hh0, ιinv _ hy, ιinv _ hW, ιinv _ hW', ← lev_mMap]
  rw [Matrix.mul_inv_rev (ιLev k 1 ρ (y * h0)⁻¹ * a) (ιLev k 1 ρ (y * h0)),
    Matrix.mul_inv_rev (ιLev k 1 ρ (y * h0)⁻¹) a, ιinv _ hW, ιinv _ (Matrix.isUnit_nonsing_inv_det _ hW),
    Matrix.nonsing_inv_nonsing_inv _ hW]
  simp only [mul_assoc]
  rw [hLw, hRw, hW1, hW2]

theorem psi_Qm (ρ : ℕ) {z0 : Fin (2 * ρ + k + 1) → ℂ} (hz0 : inWb k ρ z0) {a : Mt k (1 + ρ)} {y : Mt k ρ}
    (ha : Matrix.of a ∈ Nset k (1 + ρ)) (hy : Matrix.of y ∈ Nset k ρ) :
    psi k (ρ + 1) (D.castV (Nat.add_comm 1 ρ) (liftVec k 1 ρ z0)) cStd (Matrix.of (Qm ρ (a, y))) =
      psi k (ρ + 1) (D.castV (Nat.add_comm 1 ρ) (liftVec k 1 ρ z0)) cStd (D.castM (Nat.add_comm 1 ρ) (Matrix.of a)) *
        psi k ρ z0 cStd (Matrix.of y) := by
  show psi k (ρ + 1) (D.castV (Nat.add_comm 1 ρ) (liftVec k 1 ρ z0)) cStd
      (D.castM (Nat.add_comm 1 ρ) (Matrix.of a * ιLev k 1 ρ (Matrix.of y))) = _
  rw [psi_castM, psi_castM, Qx4.psi_mul (Qx4.lift_inWb hz0) ha (B2x6.lev_n hy), Qx4.psi_lev]

theorem psi_conjLev (ρ : ℕ) {z0 : Fin (2 * ρ + k + 1) → ℂ} (hz0 : inWb k ρ z0) {a : B.Mat k (1 + ρ)}
    {y h0 : B.Mat k ρ} (ha : a ∈ Nset k (1 + ρ)) (hy : y ∈ Nset k ρ) (hh0 : h0 ∈ UWset k ρ z0) :
    psi k (1 + ρ) (liftVec k 1 ρ z0) cStd ((ιLev k 1 ρ (y * h0))⁻¹ * a * ιLev k 1 ρ (y * h0)) =
      psi k (1 + ρ) (liftVec k 1 ρ z0) cStd a := by
  have hz1 := Qx4.lift_inWb hz0
  have hyN : ιLev k 1 ρ y ∈ Nset k (1 + ρ) := B2x6.lev_n hy
  have hhW : ιLev k 1 ρ h0 ∈ UWset k (1 + ρ) (liftVec k 1 ρ z0) := Dx2.Tower.lev_UW 1 ρ z0 h0 hh0
  have hu : (ιLev k 1 ρ y)⁻¹ * a * ιLev k 1 ρ y ∈ Nset k (1 + ρ) :=
    WeylGroupFacts.mem_n_mul (WeylGroupFacts.mem_n_mul (WeylGroupFacts.mem_n_inv hyN) ha) hyN
  have e : (ιLev k 1 ρ (y * h0))⁻¹ * a * ιLev k 1 ρ (y * h0) =
      (ιLev k 1 ρ h0)⁻¹ * ((ιLev k 1 ρ y)⁻¹ * a * ιLev k 1 ρ y) * ιLev k 1 ρ h0 := by
    rw [Dx2.Tower.lev_mul, Matrix.mul_inv_rev]; simp only [Matrix.mul_assoc]
  rw [e, Qx4.psi_conjW' hz1 hhW hu, Qx4.psi_conjN' hz1 hyN ha]

theorem heis_conj_inv (ρ : ℕ) {g : B.Mat k ρ} (hg : g ∈ B.GV k ρ) (x : B2.HPar k ρ) :
    (ιLev k 1 ρ g)⁻¹ * B2.heis0 k ρ x * ιLev k 1 ρ g = B2.heis0 k ρ (g⁻¹ *ᵥ x.1, x.2) := by
  have hu : IsUnit g.det := HermitianFormFactor.UH_unit (Ux3.hpk_det k ρ) hg
  have hgi : g⁻¹ ∈ B.GV k ρ := HermitianFormFactor.UH_inv (Ux3.hpk_det k ρ) hg
  have h := Formalism.FourierDecayAlt.P.heisenberg_conjugation_by_levi k ρ g⁻¹ hgi x
  rwa [LongWeylElement.lev_inv _ hu, Matrix.nonsing_inv_nonsing_inv _ (LongWeylElement.lev_unit _ hu)] at h

theorem heis_meas_conj_inv (ρ : ℕ) {g : B.Mat k ρ} (hg : g ∈ B.GV k ρ) :
    (B2.μHeis k ρ).map (conjM ((ιLev k 1 ρ g)⁻¹)) = B2.μHeis k ρ := by
  have hu : IsUnit g.det := HermitianFormFactor.UH_unit (Ux3.hpk_det k ρ) hg
  have hgi : g⁻¹ ∈ B.GV k ρ := HermitianFormFactor.UH_inv (Ux3.hpk_det k ρ) hg
  have h := Formalism.FourierDecayAlt.P.heisenberg_levi_conjugation_measure k ρ g⁻¹ hgi
  rwa [LongWeylElement.lev_inv _ hu] at h

end Formalism.FourierDecayAlt.P.PBH
