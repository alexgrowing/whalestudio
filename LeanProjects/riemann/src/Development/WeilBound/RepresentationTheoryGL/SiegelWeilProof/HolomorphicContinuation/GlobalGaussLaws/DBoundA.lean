import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DBound

noncomputable section

open Matrix Topology Filter
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.Glob

namespace DBoundAH

variable {n : ℕ}

def rowC {m : ℕ} (u : Fin m → Fin n → ℂ) (a : Fin m) : Fin n → ℂ := fun j => star (u a j)

theorem trace_gramB {m : ℕ} (Z : Matrix (Fin n) (Fin n) ℂ) (ε : Fin m → Bool) (b : Bool) (u : Fin m → Fin n → ℂ) :
    (Z * gramB ε b u).trace = ∑ a ∈ Finset.univ.filter (fun a => ε a = b),
      star (rowC u a) ⬝ᵥ (Z *ᵥ rowC u a) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, gramB, evX, Qb, map_sum, map_mul, MvPolynomial.eval_X,
    dotProduct, Matrix.mulVec, rowC, Pi.star_apply, star_star, Finset.mul_sum, Finset.sum_mul]
  simp only [Bool.true_eq_false, if_true, if_false]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun a _ => ?_))
  simp only [Bool.false_eq_true, if_false]
  ring

theorem star_dot_conjTranspose (Z : Matrix (Fin n) (Fin n) ℂ) (w : Fin n → ℂ) :
    star w ⬝ᵥ (Zᴴ *ᵥ w) = star (star w ⬝ᵥ (Z *ᵥ w)) := by
  simp only [dotProduct, mulVec, conjTranspose_apply, Pi.star_apply, star_sum, star_mul', star_star, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem im_eq_re (Z : Matrix (Fin n) (Fin n) ℂ) (w : Fin n → ℂ) :
    (star w ⬝ᵥ (Z *ᵥ w)).im = (star w ⬝ᵥ (((-(Complex.I / 2)) • (Z - Zᴴ)) *ᵥ w)).re := by
  rw [Matrix.smul_mulVec, Matrix.sub_mulVec, dotProduct_smul, dotProduct_sub, star_dot_conjTranspose]
  simp only [smul_eq_mul, Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.div_ofNat_re,
    Complex.div_ofNat_im, Complex.I_re, Complex.I_im, Complex.sub_re, Complex.sub_im, Complex.star_def,
    Complex.conj_re, Complex.conj_im]
  ring

private theorem norm_star_dotProduct_mulVec_le_sum_norm_mul (M : Matrix (Fin n) (Fin n) ℂ) (w : Fin n → ℂ) :
    ‖star w ⬝ᵥ (M *ᵥ w)‖ ≤ (∑ i, ∑ j, ‖M i j‖) * ∑ j, ‖w j‖ ^ 2 := by
  have hS : ∀ i j, ‖w i‖ * ‖w j‖ ≤ ∑ k, ‖w k‖ ^ 2 := by
    intro i j
    have hi : ‖w i‖ ^ 2 ≤ ∑ k, ‖w k‖ ^ 2 :=
      Finset.single_le_sum (f := fun k => ‖w k‖ ^ 2) (fun k _ => by positivity) (Finset.mem_univ i)
    have hj : ‖w j‖ ^ 2 ≤ ∑ k, ‖w k‖ ^ 2 :=
      Finset.single_le_sum (f := fun k => ‖w k‖ ^ 2) (fun k _ => by positivity) (Finset.mem_univ j)
    nlinarith [sq_nonneg (‖w i‖ - ‖w j‖), norm_nonneg (w i), norm_nonneg (w j)]
  calc ‖star w ⬝ᵥ (M *ᵥ w)‖ = ‖∑ i, ∑ j, star (w i) * (M i j * w j)‖ := by
        simp [dotProduct, Matrix.mulVec, Finset.mul_sum]
    _ ≤ ∑ i, ∑ j, ‖star (w i) * (M i j * w j)‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)
    _ = ∑ i, ∑ j, ‖M i j‖ * (‖w i‖ * ‖w j‖) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
          rw [norm_mul, norm_mul, norm_star]
          ring
    _ ≤ ∑ i, ∑ j, ‖M i j‖ * ∑ k, ‖w k‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (hS i j) (norm_nonneg _)
    _ = (∑ i, ∑ j, ‖M i j‖) * ∑ k, ‖w k‖ ^ 2 := by simp [Finset.sum_mul]

private theorem exists_pos_mul_sum_sq_le_re_of_posDef (H0 : Matrix (Fin n) (Fin n) ℂ) (h0 : H0.PosDef) :
    ∃ c > 0, ∀ w : Fin n → ℂ, c * ∑ j, ‖w j‖ ^ 2 ≤ (star w ⬝ᵥ (H0 *ᵥ w)).re := by
  classical
  have hA := h0.1
  have hspec : H0 = (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
      Matrix.diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) * star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) := by
    have := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  obtain ⟨c, hc, hcle⟩ : ∃ c > 0, ∀ i, c ≤ hA.eigenvalues i := by
    rcases isEmpty_or_nonempty (Fin n) with hn | hn
    · exact ⟨1, one_pos, fun i => (IsEmpty.false i).elim⟩
    · obtain ⟨i0, _, hi0⟩ := Finset.exists_min_image Finset.univ hA.eigenvalues Finset.univ_nonempty
      exact ⟨hA.eigenvalues i0, h0.eigenvalues_pos i0, fun i => hi0 i (Finset.mem_univ i)⟩
  refine ⟨c, hc, fun w => ?_⟩
  have hsv : star w ᵥ* (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) =
      star (star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *ᵥ w) := by
    rw [Matrix.star_mulVec, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
  have h1 : star w ⬝ᵥ (H0 *ᵥ w) = ∑ i, ((hA.eigenvalues i : ℝ) : ℂ) *
      (star ((star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *ᵥ w) i) *
        ((star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *ᵥ w) i)) := by
    conv_lhs => rw [hspec]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, hsv]
    simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have h2 : star (star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *ᵥ w) ⬝ᵥ
      (star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *ᵥ w) = star w ⬝ᵥ w := by
    rw [← hsv, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Unitary.mul_star_self_of_mem (hA.eigenvectorUnitary).2, Matrix.one_mulVec]
  have hre : ∀ z : ℂ, (star z * z).re = ‖z‖ ^ 2 := by
    intro z
    rw [Complex.star_def, Complex.conj_mul']
    norm_cast
  have h2' : ∑ i, ‖(star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *ᵥ w) i‖ ^ 2 = ∑ j, ‖w j‖ ^ 2 := by
    have := congrArg Complex.re h2
    simp only [dotProduct, Pi.star_apply, Complex.re_sum, hre] at this
    exact this
  rw [h1, Complex.re_sum, ← h2', Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Complex.re_ofReal_mul, hre]
  exact mul_le_mul_of_nonneg_right (hcle i) (by positivity)

theorem posDef_unif {P : Type} [TopologicalSpace P] {p₀ : P} (H : P → Matrix (Fin n) (Fin n) ℂ)
    (hH : ∀ i j, ContinuousAt (fun p => H p i j) p₀) (h0 : (H p₀).PosDef) :
    ∃ δ > 0, ∀ᶠ p in 𝓝 p₀, ∀ w : Fin n → ℂ, δ * ∑ j, ‖w j‖ ^ 2 ≤ (star w ⬝ᵥ (H p *ᵥ w)).re := by
  obtain ⟨c, hc, hcoer⟩ := exists_pos_mul_sum_sq_le_re_of_posDef (H p₀) h0
  have hf : Tendsto (fun p => ∑ i, ∑ j, ‖H p i j - H p₀ i j‖) (𝓝 p₀) (𝓝 0) := by
    have h00 : (0 : ℝ) = ∑ i : Fin n, ∑ j : Fin n, ‖H p₀ i j - H p₀ i j‖ := by simp
    rw [h00]
    exact tendsto_finset_sum _ fun i _ => tendsto_finset_sum _ fun j _ =>
      ((hH i j).tendsto.sub tendsto_const_nhds).norm
  have hev := (tendsto_order.1 hf).2 (c / 2) (by positivity)
  refine ⟨c / 2, by positivity, hev.mono fun p hp w => ?_⟩
  have hb := norm_star_dotProduct_mulVec_le_sum_norm_mul (H p - H p₀) w
  have hsplit : (star w ⬝ᵥ (H p *ᵥ w)).re =
      (star w ⬝ᵥ (H p₀ *ᵥ w)).re + (star w ⬝ᵥ ((H p - H p₀) *ᵥ w)).re := by
    rw [Matrix.sub_mulVec, dotProduct_sub]
    simp
  have hlow : -‖star w ⬝ᵥ ((H p - H p₀) *ᵥ w)‖ ≤ (star w ⬝ᵥ ((H p - H p₀) *ᵥ w)).re :=
    (abs_le.mp (Complex.abs_re_le_norm _)).1
  have hS : 0 ≤ ∑ j, ‖w j‖ ^ 2 := Finset.sum_nonneg fun j _ => by positivity
  have hcw := hcoer w
  have hp' : ∑ i, ∑ j, ‖(H p - H p₀) i j‖ < c / 2 := by simpa [Matrix.sub_apply] using hp
  have hK := mul_le_mul_of_nonneg_right hp'.le hS
  linarith

end DBoundAH

end PositivityTheory.Rg.Sw.Glob
