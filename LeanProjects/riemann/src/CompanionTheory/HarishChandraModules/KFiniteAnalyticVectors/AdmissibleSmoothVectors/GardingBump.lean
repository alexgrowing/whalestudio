import Formalism.PeriodIntegrals.UpqRep

open Matrix Topology Set Filter
open scoped ContDiff

noncomputable section

namespace CompanionTheory.D.gk.admitted.Gard

open PI.UpqRep

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem contDiff_entry (i j : Fin n) : ContDiff ℝ ∞ fun y : Matrix (Fin n) (Fin n) ℂ => y i j :=
  contDiff_apply_apply ℝ ℂ i j

theorem contDiff_hs : ContDiff ℝ ∞ (hs : Matrix (Fin n) (Fin n) ℂ → ℝ) := by
  unfold hs
  exact ContDiff.sum fun i _ => ContDiff.sum fun j _ => (contDiff_entry i j).norm_sq ℝ

theorem contDiff_mul :
    ContDiff ℝ ∞ fun p : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ => p.1 * p.2 := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  simp only [Matrix.mul_apply]
  exact ContDiff.sum fun k _ => ((contDiff_entry i k).comp contDiff_fst).mul ((contDiff_entry k j).comp contDiff_snd)

theorem hs_eq_trace (y : Matrix (Fin n) (Fin n) ℂ) : (hs y : ℂ) = (y * yᴴ).trace := by
  simp only [hs, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  push_cast
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rfl

theorem hs_conj {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (y : Matrix (Fin n) (Fin n) ℂ) : hs (kᴴ * y * k) = hs y := by
  have h1 : k * kᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hk
  apply Complex.ofReal_injective
  rw [hs_eq_trace, hs_eq_trace]
  have : kᴴ * y * k * (kᴴ * y * k)ᴴ = kᴴ * (y * yᴴ * k) := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc k kᴴ, h1, Matrix.one_mul]
  rw [this, Matrix.trace_mul_comm, Matrix.mul_assoc, h1, Matrix.mul_one]

theorem norm_le_of_hs {y : Matrix (Fin n) (Fin n) ℂ} {r : ℝ} (hr : 0 ≤ r) (h : hs y ≤ r ^ 2) : ‖y‖ ≤ r := by
  rw [Matrix.norm_le_iff hr]
  intro i j
  have h1 : ‖y i j‖ ^ 2 ≤ ∑ j, ‖y i j‖ ^ 2 :=
    Finset.single_le_sum (f := fun j => ‖y i j‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j)
  have h2 : ∑ j, ‖y i j‖ ^ 2 ≤ hs y :=
    Finset.single_le_sum (f := fun i => ∑ j, ‖y i j‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ i)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hr two_ne_zero).1 (h1.trans (h2.trans h))

theorem exists_bump {W : Set (Matrix (Fin n) (Fin n) ℂ)} (hW : W ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ)) :
    ∃ (f : Matrix (Fin n) (Fin n) ℂ → ℝ) (S : Set (Matrix (Fin n) (Fin n) ℂ)), ContDiff ℝ ∞ f ∧ 0 ≤ f ∧ f 1 ≠ 0 ∧
      IsCompact S ∧ S ⊆ W ∧ (∀ y, f y ≠ 0 → y ∈ S) ∧
      ∀ k ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ y, f (kᴴ * y * k) = f y := by
  obtain ⟨r, hr, hrW⟩ := Metric.nhds_basis_closedBall.mem_iff.1 hW
  refine ⟨fun y => expNegInvGlue (r ^ 2 - hs (y - 1)), Metric.closedBall 1 r, ?_, fun y => expNegInvGlue.nonneg _,
    ?_, isCompact_closedBall _ _, hrW, fun y hy => ?_, fun k hk y => ?_⟩
  · exact expNegInvGlue.contDiff.comp (contDiff_const.sub (contDiff_hs.comp (contDiff_id.sub contDiff_const)))
  · refine (expNegInvGlue.pos_of_pos ?_).ne'
    simp only [sub_self, hs, Matrix.zero_apply, norm_zero]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero, sub_zero]
    positivity
  · rw [mem_closedBall_iff_norm]
    refine norm_le_of_hs hr.le ?_
    by_contra h
    exact hy (expNegInvGlue.zero_of_nonpos (by linarith))
  · have h1 : kᴴ * k = 1 := Matrix.mem_unitaryGroup_iff'.1 hk
    have : kᴴ * y * k - 1 = kᴴ * (y - 1) * k := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h1]
    simp only [this, hs_conj hk]

theorem isCompact_mul_inv {A S : Set (Matrix (Fin n) (Fin n) ℂ)} (hA : IsCompact A) (hS : IsCompact S)
    (hd : ∀ B ∈ S, B.det ≠ 0) :
    IsCompact ((fun p : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ => p.1 * p.2⁻¹) '' (A ×ˢ S)) := by
  refine (hA.prod hS).image_of_continuousOn fun p hp => ?_
  have h1 : ContinuousAt (Inv.inv : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) p.2 := by
    refine continuousAt_matrix_inv _ ?_
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ (hd _ hp.2)
  exact (continuousAt_fst.mul (h1.comp continuousAt_snd)).continuousWithinAt

end CompanionTheory.D.gk.admitted.Gard
