import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DensityLemma.PFibreBoundHH
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DensityLemma.PFibreBoundV
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DensityLemma.PFibreBoundW
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists

open MeasureTheory Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
open scoped ENNReal NNReal

noncomputable section

namespace PI.UnitaryGroupMassFormula.DLm

namespace HBx

variable {k r : ℕ}

end HBx

namespace HBx

variable {k r : ℕ}

lemma uMap_cont (z : Fin (2 * r + k + 1) → ℂ) : Continuous fun s : B.Mat k r => C2.uMap k r z s := by
  unfold C2.uMap herm
  refine continuous_pi fun a => continuous_pi fun b => ?_
  by_cases h : a.val < r
  · simp only [dif_pos h]
    exact continuous_const.dotProduct (continuous_const.matrix_mulVec
      (continuous_id.matrix_mulVec continuous_const))
  · simp only [dif_neg h]
    exact (continuous_const.dotProduct (continuous_const.matrix_mulVec
      (continuous_id.matrix_mulVec continuous_const))).div_const _

lemma isClosed_N0set (z : Fin (2 * r + k + 1) → ℂ) : IsClosed (C2.N0set k r z) := by
  have hU : IsClosed (UH (Hpk k r)) := by
    show IsClosed {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ | gᴴ * Hpk k r * g = Hpk k r}
    exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
      continuous_id) continuous_const
  have hA : IsClosed {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ | ∀ (a : Fin r) (i : Fin (2 * r + k + 1)), a.val ≤ i.val →
      g i (eI k r a) = if i = eI k r a then 1 else 0} := by
    have e : {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ | ∀ (a : Fin r) (i : Fin (2 * r + k + 1)), a.val ≤ i.val →
        g i (eI k r a) = if i = eI k r a then 1 else 0} =
        ⋂ (a : Fin r) (i : Fin (2 * r + k + 1)) (_ : a.val ≤ i.val),
          {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ | g i (eI k r a) = if i = eI k r a then 1 else 0} := by
      ext g
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rw [e]
    exact isClosed_iInter fun a => isClosed_iInter fun i => isClosed_iInter fun _ =>
      isClosed_eq (continuous_id.matrix_elem _ _) continuous_const
  have hB : IsClosed {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ | ∀ i j : Fin (2 * r + k + 1), r ≤ j.val → j.val ≤ r + k → r ≤ i.val →
      g i j = if i = j then 1 else 0} := by
    have e : {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ | ∀ i j : Fin (2 * r + k + 1), r ≤ j.val → j.val ≤ r + k → r ≤ i.val →
        g i j = if i = j then 1 else 0} =
        ⋂ (i : Fin (2 * r + k + 1)) (j : Fin (2 * r + k + 1)) (_ : r ≤ j.val) (_ : j.val ≤ r + k)
          (_ : r ≤ i.val), {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ | g i j = if i = j then 1 else 0} := by
      ext g
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rw [e]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_iInter fun _ => isClosed_iInter fun _ =>
        isClosed_eq (continuous_id.matrix_elem _ _) continuous_const
  have hu : IsClosed {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ | C2.uMap k r z g = 1} := isClosed_eq (uMap_cont z) continuous_const
  have e : C2.N0set k r z = ((UH (Hpk k r) ∩ {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ | ∀ (a : Fin r) (i : Fin (2 * r + k + 1)),
      a.val ≤ i.val → g i (eI k r a) = if i = eI k r a then 1 else 0}) ∩
      {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ | ∀ i j : Fin (2 * r + k + 1), r ≤ j.val → j.val ≤ r + k → r ≤ i.val →
        g i j = if i = j then 1 else 0}) ∩ {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ | C2.uMap k r z g = 1} := by
    ext g
    unfold C2.N0set Formalism.QuantumDeterminants.Nset
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
    tauto
  rw [e]
  exact ((hU.inter hA).inter hB).inter hu

lemma blk_zero : unipotentBlockMatrix k r 0 0 = 1 := by
  ext i j
  simp [unipotentBlockMatrix, cmOf, Matrix.one_apply]

lemma skew_mul (Ba B : Matrix (Fin r) (Fin (k + 1)) ℂ) (Sa S : Matrix (Fin r) (Fin r) ℂ) (hSa : Saᴴ = -Sa)
    (hS : Sᴴ = -S) :
    (Sa + S + (1 / 2 : ℂ) • (B * Matrix.diagonal (hW k) * Baᴴ - Ba * Matrix.diagonal (hW k) * Bᴴ))ᴴ =
      -(Sa + S + (1 / 2 : ℂ) • (B * Matrix.diagonal (hW k) * Baᴴ - Ba * Matrix.diagonal (hW k) * Bᴴ)) := by
  have hD : (Matrix.diagonal (hW k))ᴴ = Matrix.diagonal (hW k) := by
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext j
    unfold hW
    split_ifs with hj <;> simp [hj]
  have hX : (B * Matrix.diagonal (hW k) * Baᴴ)ᴴ = Ba * Matrix.diagonal (hW k) * Bᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hD, Matrix.mul_assoc]
  have hY : (Ba * Matrix.diagonal (hW k) * Bᴴ)ᴴ = B * Matrix.diagonal (hW k) * Baᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hD, Matrix.mul_assoc]
  have hc : star (1 / 2 : ℂ) = 1 / 2 := by simp
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_sub, hX, hY, hSa, hS, hc,
    ← neg_sub (B * Matrix.diagonal (hW k) * Baᴴ) (Ba * Matrix.diagonal (hW k) * Bᴴ), smul_neg]
  abel

end HBx

theorem unipotent_integral_closed : UnipotentSetIsClosedSubgroup := by
  intro k r z hz
  have key : ∀ (Bm : Matrix (Fin r) (Fin (k + 1)) ℂ) (S : Matrix (Fin r) (Fin r) ℂ),
      unipotentBlockMatrix k r Bm S * unipotentBlockMatrix k r (-Bm) (-S) = 1 := by
    intro Bm S
    rw [NBk.nbm_mul]
    have e1 : Bm + -Bm = 0 := add_neg_cancel Bm
    have e2 : S + -S + (1 / 2 : ℂ) • (-Bm * Matrix.diagonal (hW k) * Bmᴴ -
        Bm * Matrix.diagonal (hW k) * (-Bm)ᴴ) = 0 := by
      simp [Matrix.conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg]
    rw [e1, e2, HBx.blk_zero]
  refine ⟨?_, ?_, ?_, ?_, HBx.isClosed_N0set z⟩
  · rw [← HBx.blk_zero]
    exact NBk.nb_mem _ _ hz (Matrix.zero_mulVec _) (by simp)
  · intro a ha b hb
    obtain ⟨Ba, Sa, hBa, hSa, rfl⟩ := unipotent_eq_block k r z hz a ha
    obtain ⟨B, S, hB, hS, rfl⟩ := unipotent_eq_block k r z hz b hb
    rw [NBk.nbm_mul]
    exact NBk.nb_mem _ _ hz (by rw [Matrix.add_mulVec, hBa, hB, add_zero]) (HBx.skew_mul Ba B Sa S hSa hS)
  · intro a ha
    obtain ⟨Ba, Sa, hBa, hSa, rfl⟩ := unipotent_eq_block k r z hz a ha
    rw [Matrix.inv_eq_right_inv (key Ba Sa)]
    exact NBk.nb_mem _ _ hz (by rw [Matrix.neg_mulVec, hBa, neg_zero])
      (by rw [Matrix.conjTranspose_neg, hSa])
  · intro a ha
    obtain ⟨Ba, Sa, hBa, hSa, rfl⟩ := unipotent_eq_block k r z hz a ha
    exact Matrix.isUnit_det_of_right_inverse (key Ba Sa)

end PI.UnitaryGroupMassFormula.DLm
