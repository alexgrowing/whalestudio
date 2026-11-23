import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlkConjTranspose
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional

open Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.AdmGL

variable {ι : Type} [Fintype ι] [DecidableEq ι] {a n : ℕ}

theorem isClosed_range_blk (e : Fin a × ι ≃ Fin n) : IsClosed {g | blk e (unblk e g) = g} :=
  isClosed_eq ((continuous_blk e).comp (continuous_unblk e)) continuous_id

theorem blk_unblk_of_mem_closure (e : Fin a × ι ≃ Fin n) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ closure (blkG e)) : blk e (unblk e g) = g :=
  (closure_minimal (fun _ h => ((mem_blkG_iff e).1 h).2) (isClosed_range_blk e)) hg

theorem finite_setOf_det_line_eq_zero {A B : Matrix (Fin n) (Fin n) ℂ} (hA : IsUnit A) :
    {z : ℂ | ((1 - z) • A + z • B).det = 0}.Finite := by
  let P : Polynomial ℂ := Matrix.det ((1 - Polynomial.X : Polynomial ℂ) • A.map Polynomial.C
    + (Polynomial.X : Polynomial ℂ) • B.map Polynomial.C)
  have hev : ∀ z : ℂ, P.eval z = ((1 - z) • A + z • B).det := by
    intro z
    have := RingHom.map_det (Polynomial.evalRingHom z) ((1 - Polynomial.X : Polynomial ℂ) • A.map Polynomial.C
      + (Polynomial.X : Polynomial ℂ) • B.map Polynomial.C)
    simp only [Polynomial.coe_evalRingHom] at this
    rw [this]
    congr 1
    ext i j
    simp
    exact mul_comm _ _
  have hP : P ≠ 0 := by
    intro h
    have := hev 0
    rw [h] at this
    simp only [Polynomial.eval_zero, sub_zero, one_smul, zero_smul, add_zero] at this
    exact ((Matrix.isUnit_iff_isUnit_det A).1 hA).ne_zero this.symm
  refine (P.rootSet_finite ℂ).subset ?_
  intro z hz
  rw [Polynomial.mem_rootSet]
  refine ⟨hP, ?_⟩
  simpa [hev] using hz

theorem isPreconnected_blkG (e : Fin a × ι ≃ Fin n) : IsPreconnected (blkG e) := by
  refine isPreconnected_of_forall_pair ?_
  rintro _ ⟨M, hM, rfl⟩ _ ⟨N, hN, rfl⟩
  have hA : IsUnit (blk e M) := (isUnit_blk_iff e M).2 hM
  have hB : IsUnit (blk e N) := (isUnit_blk_iff e N).2 hN
  set A := blk e M
  set B := blk e N
  let Z : Set ℂ := {z | ((1 - z) • A + z • B).det = 0}
  have hZ : Z.Finite := finite_setOf_det_line_eq_zero hA
  have hconn : IsPathConnected Zᶜ := hZ.countable.isPathConnected_compl_of_one_lt_rank (by
    rw [Complex.rank_real_complex]; norm_num)
  let γ : ℂ → Matrix (Fin n) (Fin n) ℂ := fun z => (1 - z) • A + z • B
  have hγ : Continuous γ := by fun_prop
  refine ⟨γ '' Zᶜ, ?_, ⟨0, ?_, by simp [γ]⟩, ⟨1, ?_, by simp [γ]⟩, hconn.isConnected.isPreconnected.image _ hγ.continuousOn⟩
  · rintro _ ⟨z, hz, rfl⟩
    refine (mem_blkG_iff e).2 ⟨(Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hz), ?_⟩
    have : γ z = blk e ((1 - z) • M + z • N) := by simp [γ, A, B]
    rw [this, unblk_blk]
  · simpa [Z] using ((Matrix.isUnit_iff_isUnit_det A).1 hA).ne_zero
  · simpa [Z] using ((Matrix.isUnit_iff_isUnit_det B).1 hB).ne_zero

theorem blk_inv (e : Fin a × ι ≃ Fin n) {M : Matrix (Fin a) (Fin a) (ι → ℂ)} (hM : IsUnit M) :
    (blk e M)⁻¹ = blk e M⁻¹ := by
  refine Matrix.inv_eq_right_inv ?_
  rw [← blk_mul, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hM), blk_one]

theorem isLinRed_blkG (e : Fin a × ι ≃ Fin n) : GlobalTheory.LinRed.IsLinRed (blkG e) where
  one_mem := ⟨1, isUnit_one, blk_one e⟩
  mul_mem := by
    rintro _ ⟨M, hM, rfl⟩ _ ⟨N, hN, rfl⟩
    exact ⟨M * N, IsUnit.mul hM hN, blk_mul e M N⟩
  isUnit := fun g hg => ((mem_blkG_iff e).1 hg).1
  inv_mem := by
    rintro _ ⟨M, hM, rfl⟩
    refine ⟨M⁻¹, ?_, (blk_inv e hM).symm⟩
    exact (Matrix.isUnit_nonsing_inv_iff).2 hM
  closed := fun g hg hcl => (mem_blkG_iff e).2 ⟨hg, blk_unblk_of_mem_closure e hcl⟩
  connected := isPreconnected_blkG e
  star_mem := by
    rintro _ ⟨M, hM, rfl⟩
    refine ⟨Mᴴ, ?_, blk_conjTranspose e M⟩
    have : IsUnit (star M) := IsUnit.star hM
    exact this

end GlobalTheory.CompanionTheory.AdmGL

end
