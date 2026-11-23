import Formalism.RealPlaceAnalysis.Complexify

open Matrix

noncomputable section

namespace Formalism.REAL

private lemma inG_iff_star_signed_entries_eq_zero {n : ℕ} (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) :
    inG ε X ↔ ∀ i j, star (X j i) * (if ε j then 1 else -1) + (if ε i then 1 else -1) * X i j = 0 := by
  unfold inG Jm
  constructor
  · intro h i j
    have := congrFun (congrFun h i) j
    simpa only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, conjTranspose_apply,
      Matrix.zero_apply] using this
  · intro h
    ext i j
    simpa only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, conjTranspose_apply,
      Matrix.zero_apply] using h i j

lemma f1auxiliary_hs_eq {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : hs g = (trace (gᴴ * g)).re := by
  simp only [hs, Matrix.trace, Matrix.diag, Matrix.mul_apply, conjTranspose_apply, Complex.re_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [Complex.star_def, Complex.mul_re]

lemma continuous_hs_real_place_taylor {n : ℕ} : Continuous (hs : Matrix (Fin n) (Fin n) ℂ → ℝ) := by
  unfold hs
  exact continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
    ((continuous_apply j).comp (continuous_apply i)).norm.pow 2

lemma f1auxiliary_hs_one (n : ℕ) : hs (1 : Matrix (Fin n) (Fin n) ℂ) = n := by
  simp only [hs, Matrix.one_apply]
  have key : ∀ i : Fin n, ∑ j, ‖(if i = j then (1 : ℂ) else 0)‖ ^ 2 = 1 := by
    intro i
    rw [Finset.sum_eq_single i (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
    simp
  simp [key]

theorem ball_open_holds : BallOpen := by
  intro n R hR
  refine ⟨{g | hs g < R}, isOpen_lt continuous_hs_real_place_taylor continuous_const, ?_, fun g hg => hg⟩
  show hs (1 : Matrix (Fin n) (Fin n) ℂ) < R
  rw [f1auxiliary_hs_one]
  exact hR

lemma f1auxiliary_closed {n : ℕ} (ε : Fin n → Bool) : IsClosed {g : Matrix (Fin n) (Fin n) ℂ | inUJ ε g} :=
  isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
    continuous_const

lemma f1auxiliary_entry_le {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) : ‖g i j‖ ^ 2 ≤ hs g := by
  unfold hs
  calc ‖g i j‖ ^ 2 ≤ ∑ j', ‖g i j'‖ ^ 2 :=
        Finset.single_le_sum (f := fun j' => ‖g i j'‖ ^ 2) (fun k _ => by positivity) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', ‖g i' j'‖ ^ 2 :=
        Finset.single_le_sum (f := fun i' => ∑ j', ‖g i' j'‖ ^ 2)
          (fun k _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ i)

theorem hermitian_small_ball : HSBall := by
  intro n ε
  refine ⟨fun R => ?_, fun g k hk => ⟨?_, ?_⟩⟩
  · have hcpt : IsCompact (Set.pi Set.univ fun _ : Fin n =>
        Set.pi Set.univ fun _ : Fin n => Metric.closedBall (0 : ℂ) (Real.sqrt R)) :=
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
    refine hcpt.of_isClosed_subset ((f1auxiliary_closed ε).inter (isClosed_le continuous_hs_real_place_taylor continuous_const)) ?_
    rintro g ⟨_, hg⟩ i _ j _
    have h1 := (f1auxiliary_entry_le g i j).trans hg
    simpa using Real.abs_le_sqrt h1
  · have hk1 : k * kᴴ = 1 := by
      rw [← Matrix.star_eq_conjTranspose]
      exact Matrix.mem_unitaryGroup_iff.1 hk.1
    rw [f1auxiliary_hs_eq, f1auxiliary_hs_eq, conjTranspose_mul]
    congr 1
    rw [show kᴴ * gᴴ * (g * k) = kᴴ * (gᴴ * g * k) by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm, Matrix.mul_assoc, hk1, Matrix.mul_one]
  · have hk2 : kᴴ * k = 1 := by
      rw [← Matrix.star_eq_conjTranspose]
      exact Matrix.mem_unitaryGroup_iff'.1 hk.1
    rw [f1auxiliary_hs_eq, f1auxiliary_hs_eq, conjTranspose_mul]
    congr 1
    rw [show gᴴ * kᴴ * (k * g) = gᴴ * (kᴴ * k) * g by simp only [Matrix.mul_assoc], hk2, Matrix.mul_one]

end Formalism.REAL
