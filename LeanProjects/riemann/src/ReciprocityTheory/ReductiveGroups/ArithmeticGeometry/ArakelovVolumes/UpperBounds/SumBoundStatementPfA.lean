import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.SumBoundStatement

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open Matrix Topology Filter
open scoped Matrix ComplexOrder ENNReal

noncomputable section

variable {p q : ℕ}

theorem sumBdJf_mul_Jf : Jf p q * Jf p q = 1 := by
  simp [Jf, fromBlocks_multiply, ← fromBlocks_one]

theorem sumBdIsUpq_right {M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (h : IsUpq M) :
    M * Jf p q * Mᴴ = Jf p q := by
  have h1 : (Jf p q * Mᴴ * Jf p q) * M = 1 := by
    have := h; simp only [IsUpq, Matrix.mul_assoc] at this ⊢; rw [this, sumBdJf_mul_Jf]
  have h2 : M * (Jf p q * Mᴴ * Jf p q) = 1 := mul_eq_one_comm.mp h1
  calc M * Jf p q * Mᴴ = M * (Jf p q * Mᴴ * Jf p q) * Jf p q := by
        simp only [Matrix.mul_assoc, sumBdJf_mul_Jf, Matrix.mul_one]
    _ = Jf p q := by rw [h2, Matrix.one_mul]

theorem sumBdIsUpq_blocks {M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (h : IsUpq M) :
    M.toBlocks₁₁ᴴ * M.toBlocks₁₁ = 1 + M.toBlocks₂₁ᴴ * M.toBlocks₂₁ ∧
    M.toBlocks₂₂ᴴ * M.toBlocks₂₂ = 1 + M.toBlocks₁₂ᴴ * M.toBlocks₁₂ ∧
    M.toBlocks₁₁ * M.toBlocks₁₁ᴴ = 1 + M.toBlocks₁₂ * M.toBlocks₁₂ᴴ ∧
    M.toBlocks₂₂ * M.toBlocks₂₂ᴴ = 1 + M.toBlocks₂₁ * M.toBlocks₂₁ᴴ := by
  have h1 := h
  have h2 := sumBdIsUpq_right h
  rw [IsUpq, ← fromBlocks_toBlocks M] at h1
  rw [← fromBlocks_toBlocks M] at h2
  simp only [Jf, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_inj] at h1 h2
  simp at h1 h2
  obtain ⟨a1, -, -, a4⟩ := h1
  obtain ⟨b1, -, -, b4⟩ := h2
  have a4' := congrArg Neg.neg a4
  have b4' := congrArg Neg.neg b4
  rw [neg_neg] at a4' b4'
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← a1]; abel
  · rw [← a4']; abel
  · rw [← b1]; abel
  · rw [← b4']; abel

def sumBdFsq {m n : Type*} [Fintype m] [Fintype n] (X : Matrix m n ℂ) : ℝ :=
  ∑ i, ∑ j, Complex.normSq (X i j)

theorem sumBdFsq_nonneg {m n : Type*} [Fintype m] [Fintype n] (X : Matrix m n ℂ) : 0 ≤ sumBdFsq X :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

theorem sumBd_trace_ctm {m n : Type*} [Fintype m] [Fintype n] (X : Matrix m n ℂ) :
    (trace (Xᴴ * X)).re = sumBdFsq X := by
  simp only [trace, diag, mul_apply, conjTranspose_apply, sumBdFsq, Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [Complex.normSq_apply, Complex.mul_re]

theorem sumBd_trace_mct {m n : Type*} [Fintype m] [Fintype n] (X : Matrix m n ℂ) :
    (trace (X * Xᴴ)).re = sumBdFsq X := by
  simp only [trace, diag, mul_apply, conjTranspose_apply, sumBdFsq, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [Complex.normSq_apply, Complex.mul_re]

theorem sumBd_entry_le_fsq {m n : Type*} [Fintype m] [Fintype n] (X : Matrix m n ℂ) (i : m) (j : n) :
    Complex.normSq (X i j) ≤ sumBdFsq X := by
  unfold sumBdFsq
  calc Complex.normSq (X i j) ≤ ∑ j', Complex.normSq (X i j') :=
        Finset.single_le_sum (f := fun j' => Complex.normSq (X i j')) (fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ j)
    _ ≤ _ := Finset.single_le_sum (f := fun i' => ∑ j', Complex.normSq (X i' j'))
        (fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ i)

theorem sumBd_prod_one_add {ι : Type*} (s : Finset ι) (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) :
    1 + ∑ i ∈ s, x i ≤ ∏ i ∈ s, (1 + x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have h0 : 0 ≤ ∑ i ∈ s, x i := Finset.sum_nonneg fun i _ => hx i
    nlinarith [hx a]

theorem sumBd_det_one_add_ge {n : Type*} [Fintype n] [DecidableEq n] {P : Matrix n n ℂ}
    (hP : P.PosSemidef) : 1 + (trace P).re ≤ (det (1 + P)).re := by
  set U := hP.1.eigenvectorUnitary
  have hU : (U : Matrix n n ℂ) * star (U : Matrix n n ℂ) = 1 := Unitary.mul_star_self_of_mem U.2
  have hs : P = (U : Matrix n n ℂ) * diagonal (RCLike.ofReal ∘ hP.1.eigenvalues) *
      star (U : Matrix n n ℂ) := by
    have := hP.1.spectral_theorem; rwa [Unitary.conjStarAlgAut_apply] at this
  have hd : diagonal (fun i => 1 + ((hP.1.eigenvalues i : ℝ) : ℂ)) =
      1 + diagonal (RCLike.ofReal ∘ hP.1.eigenvalues) := by
    rw [← diagonal_one, diagonal_add]; rfl
  have h1 : 1 + P = (U : Matrix n n ℂ) * diagonal (fun i => 1 + ((hP.1.eigenvalues i : ℝ) : ℂ)) *
      star (U : Matrix n n ℂ) := by
    rw [hd, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hU, ← hs]
  have hdet : det (1 + P) = ∏ i, (1 + ((hP.1.eigenvalues i : ℝ) : ℂ)) := by
    rw [h1, det_mul, det_mul, det_diagonal]
    have : det (U : Matrix n n ℂ) * det (star (U : Matrix n n ℂ)) = 1 := by rw [← det_mul, hU, det_one]
    linear_combination (∏ i, (1 + ((hP.1.eigenvalues i : ℝ) : ℂ))) * this
  have htr : (trace P).re = ∑ i, hP.1.eigenvalues i := by
    rw [hP.1.trace_eq_sum_eigenvalues]; simp
  rw [hdet, htr]
  have : (∏ i, (1 + ((hP.1.eigenvalues i : ℝ) : ℂ))) = ((∏ i, (1 + hP.1.eigenvalues i) : ℝ) : ℂ) := by
    push_cast; rfl
  rw [this, Complex.ofReal_re]
  exact sumBd_prod_one_add _ _ hP.eigenvalues_nonneg

theorem sumBd_star_mul_self_re (z : ℂ) : (star z * z).re = Complex.normSq z := by
  simp [Complex.normSq_apply, Complex.mul_re]

theorem sumBd_normSq_det (D : Matrix (Fin q) (Fin q) ℂ) :
    (det (Dᴴ * D)).re = Complex.normSq (det D) := by
  rw [det_mul, det_conjTranspose, sumBd_star_mul_self_re]

theorem sumBd_detD_ge {M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (h : IsUpq M) :
    1 + sumBdFsq M.toBlocks₁₂ ≤ Complex.normSq (det M.toBlocks₂₂) := by
  rw [← sumBd_normSq_det, (sumBdIsUpq_blocks h).2.1, ← sumBd_trace_ctm]
  exact sumBd_det_one_add_ge (posSemidef_conjTranspose_mul_self _)

theorem sumBd_entry_bound {M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (h : IsUpq M)
    (i j : Fin p ⊕ Fin q) :
    Complex.normSq (M i j) ≤ ((p + q : ℕ) + 1 : ℝ) * Complex.normSq (det M.toBlocks₂₂) := by
  obtain ⟨e1, e2, e3, e4⟩ := sumBdIsUpq_blocks h
  have hB := sumBd_detD_ge h
  have hBn := sumBdFsq_nonneg M.toBlocks₁₂
  have fD : sumBdFsq M.toBlocks₂₂ = q + sumBdFsq M.toBlocks₁₂ := by
    rw [← sumBd_trace_ctm, e2, trace_add, Complex.add_re, sumBd_trace_ctm]; simp
  have fA : sumBdFsq M.toBlocks₁₁ = p + sumBdFsq M.toBlocks₁₂ := by
    rw [← sumBd_trace_mct, e3, trace_add, Complex.add_re, sumBd_trace_mct]; simp
  have fA' : sumBdFsq M.toBlocks₁₁ = p + sumBdFsq M.toBlocks₂₁ := by
    rw [← sumBd_trace_ctm, e1, trace_add, Complex.add_re, sumBd_trace_ctm]; simp
  have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have key : ∀ X : ℝ, X ≤ (p + q : ℝ) + sumBdFsq M.toBlocks₁₂ →
      X ≤ ((p + q : ℕ) + 1 : ℝ) * Complex.normSq (det M.toBlocks₂₂) := by
    intro X hX; push_cast
    have hN1 : 1 ≤ Complex.normSq (det M.toBlocks₂₂) := by linarith
    nlinarith [mul_nonneg (add_nonneg hp hq) (sub_nonneg.mpr hN1)]
  apply key
  rcases i with a | a <;> rcases j with b | b
  · have := sumBd_entry_le_fsq M.toBlocks₁₁ a b
    exact le_trans this (by linarith)
  · have := sumBd_entry_le_fsq M.toBlocks₁₂ a b
    exact le_trans this (by linarith)
  · have := sumBd_entry_le_fsq M.toBlocks₂₁ a b
    exact le_trans this (by linarith)
  · have := sumBd_entry_le_fsq M.toBlocks₂₂ a b
    exact le_trans this (by linarith)

theorem sumBd_weight {M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (h : IsUpq M) :
    det M.toBlocks₂₂ ≠ 0 ∧
    (1 - (M.toBlocks₁₂ * M.toBlocks₂₂⁻¹) * (M.toBlocks₁₂ * M.toBlocks₂₂⁻¹)ᴴ).det.re =
      (Complex.normSq (det M.toBlocks₂₂))⁻¹ := by
  have e2 : M.toBlocks₂₂ᴴ * M.toBlocks₂₂ = 1 + M.toBlocks₁₂ᴴ * M.toBlocks₁₂ :=
    (sumBdIsUpq_blocks h).2.1
  have hD1 : 1 ≤ Complex.normSq (det M.toBlocks₂₂) := by
    have := sumBd_detD_ge h; linarith [sumBdFsq_nonneg M.toBlocks₁₂]
  set B := M.toBlocks₁₂
  set D := M.toBlocks₂₂
  have hD0 : det D ≠ 0 := by intro h0; rw [h0] at hD1; simp at hD1; linarith
  have hDu : IsUnit (det D) := isUnit_iff_ne_zero.mpr hD0
  refine ⟨hD0, ?_⟩
  have hinv : D * D⁻¹ = 1 := mul_nonsing_inv D hDu
  have hinvH : (D⁻¹)ᴴ * Dᴴ = 1 := by rw [← conjTranspose_mul, hinv, conjTranspose_one]
  have hW : 1 - (B * D⁻¹)ᴴ * (B * D⁻¹) = (D⁻¹)ᴴ * D⁻¹ := by
    have hBB : Bᴴ * B = Dᴴ * D - 1 := by rw [e2]; abel
    rw [conjTranspose_mul]
    calc 1 - (D⁻¹)ᴴ * Bᴴ * (B * D⁻¹) = 1 - (D⁻¹)ᴴ * (Bᴴ * B) * D⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = 1 - ((D⁻¹)ᴴ * Dᴴ) * (D * D⁻¹) + (D⁻¹)ᴴ * D⁻¹ := by
          rw [hBB]; simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]
          abel
      _ = (D⁻¹)ᴴ * D⁻¹ := by rw [hinv, hinvH, Matrix.one_mul]; abel
  rw [det_one_sub_mul_comm, hW, det_mul, det_conjTranspose, sumBd_star_mul_self_re,
    det_nonsing_inv, Ring.inverse_eq_inv', map_inv₀]

theorem sumBd_exists_S {n : Type*} [Fintype n] [DecidableEq n] {H : Matrix n n ℂ} (hH : H.PosDef) :
    ∃ S : Matrix n n ℂ, Sᴴ * H * S = 1 := by
  set U := hH.1.eigenvectorUnitary
  have hU : (U : Matrix n n ℂ)ᴴ * (U : Matrix n n ℂ) = 1 := by
    rw [← star_eq_conjTranspose]; exact Unitary.star_mul_self_of_mem U.2
  have hs : H = (U : Matrix n n ℂ) * diagonal (RCLike.ofReal ∘ hH.1.eigenvalues) *
      (U : Matrix n n ℂ)ᴴ := by
    have := hH.1.spectral_theorem; rwa [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose] at this
  let d : n → ℂ := fun i => (((Real.sqrt (hH.1.eigenvalues i))⁻¹ : ℝ) : ℂ)
  refine ⟨(U : Matrix n n ℂ) * diagonal d, ?_⟩
  have hdH : (diagonal d)ᴴ = diagonal d := by
    rw [diagonal_conjTranspose]; congr 1; funext i; simp [d]
  rw [conjTranspose_mul, hdH, hs]
  calc diagonal d * (U : Matrix n n ℂ)ᴴ * ((U : Matrix n n ℂ) * diagonal (RCLike.ofReal ∘ hH.1.eigenvalues) *
        (U : Matrix n n ℂ)ᴴ) * ((U : Matrix n n ℂ) * diagonal d)
      = diagonal d * ((U : Matrix n n ℂ)ᴴ * (U : Matrix n n ℂ)) * diagonal (RCLike.ofReal ∘ hH.1.eigenvalues) *
        ((U : Matrix n n ℂ)ᴴ * (U : Matrix n n ℂ)) * diagonal d := by simp only [Matrix.mul_assoc]
    _ = diagonal d * diagonal (RCLike.ofReal ∘ hH.1.eigenvalues) * diagonal d := by
        rw [hU, Matrix.mul_one, Matrix.mul_one]
    _ = 1 := by
        rw [diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
        congr 1; funext i
        have hl := hH.eigenvalues_pos i
        have hsq := Real.mul_self_sqrt hl.le
        have hs0 : 0 < Real.sqrt (hH.1.eigenvalues i) := Real.sqrt_pos.mpr hl
        simp only [d, Function.comp_apply]
        rw [show ((((Real.sqrt (hH.1.eigenvalues i))⁻¹ : ℝ) : ℂ) * (RCLike.ofReal (hH.1.eigenvalues i) : ℂ) *
            (((Real.sqrt (hH.1.eigenvalues i))⁻¹ : ℝ) : ℂ)) =
            (((Real.sqrt (hH.1.eigenvalues i))⁻¹ * hH.1.eigenvalues i * (Real.sqrt (hH.1.eigenvalues i))⁻¹ : ℝ) : ℂ)
            by push_cast; rfl]
        rw [← hsq]; field_simp; simp [hs0.ne']

theorem sumBd_posDef_swap {Z : Matrix (Fin p) (Fin q) ℂ} (hZ : (1 - Z * Zᴴ).PosDef) :
    (1 - Zᴴ * Z).PosDef := by
  set P := 1 - Z * Zᴴ
  have hQ : (1 + Zᴴ * P⁻¹ * Z).PosDef :=
    PosDef.one.add_posSemidef (hZ.inv.posSemidef.conjTranspose_mul_mul_same Z)
  have hPi : P * P⁻¹ = 1 := mul_nonsing_inv P (isUnit_iff_ne_zero.mpr hZ.det_pos.ne')
  have hm : (1 + Zᴴ * P⁻¹ * Z) * (1 - Zᴴ * Z) = 1 := by
    have : Zᴴ * P⁻¹ * Z - Zᴴ * P⁻¹ * (Z * Zᴴ) * Z = Zᴴ * Z := by
      calc Zᴴ * P⁻¹ * Z - Zᴴ * P⁻¹ * (Z * Zᴴ) * Z = Zᴴ * (P⁻¹ * (1 - Z * Zᴴ)) * Z := by
            simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]
        _ = Zᴴ * Z := by
            rw [nonsing_inv_mul P (isUnit_iff_ne_zero.mpr hZ.det_pos.ne'), Matrix.mul_one]
    calc (1 + Zᴴ * P⁻¹ * Z) * (1 - Zᴴ * Z)
        = 1 - Zᴴ * Z + (Zᴴ * P⁻¹ * Z - Zᴴ * P⁻¹ * (Z * Zᴴ) * Z) := by
          simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
          abel
      _ = 1 := by rw [this]; abel
  have hm' : (1 - Zᴴ * Z) * (1 + Zᴴ * P⁻¹ * Z) = 1 := mul_eq_one_comm.mp hm
  rw [← inv_eq_left_inv hm']
  exact hQ.inv

theorem sumBd_isUpq_mul {g G : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (hg : IsUpq g) (hG : IsUpq G) :
    IsUpq (g * G) := by
  unfold IsUpq at *
  rw [conjTranspose_mul]
  calc Gᴴ * gᴴ * Jf p q * (g * G) = Gᴴ * (gᴴ * Jf p q * g) * G := by simp only [Matrix.mul_assoc]
    _ = Jf p q := by rw [hg, hG]

theorem sumBd_frame {Z : Matrix (Fin p) (Fin q) ℂ} (hZ : (1 - Z * Zᴴ).PosDef) :
    ∃ G : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ, IsUpq G ∧
      ∀ g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ, IsUpq g → ∀ s : ℝ,
        dpow (mob g Z) s = ((Complex.normSq (det (g * G).toBlocks₂₂))⁻¹) ^ s := by
  obtain ⟨S1, h1⟩ := sumBd_exists_S hZ
  obtain ⟨S2, h2⟩ := sumBd_exists_S (sumBd_posDef_swap hZ)
  have hS2 : IsUnit (det S2) := by
    have := congrArg det h2; rw [det_mul, det_mul, det_one] at this
    exact isUnit_iff_ne_zero.mpr (fun h0 => by rw [h0, mul_zero] at this; exact zero_ne_one this)
  have hS2i : S2 * S2⁻¹ = 1 := mul_nonsing_inv S2 hS2
  have hG : IsUpq (fromBlocks S1 (Z * S2) (Zᴴ * S1) S2) := by
    unfold IsUpq Jf
    rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_one, Matrix.mul_zero,
      add_zero, zero_add, Matrix.mul_neg, Matrix.neg_mul]
    congr 1
    · rw [← h1]; simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]; abel
    · simp only [Matrix.mul_assoc]; abel
    · simp only [Matrix.mul_assoc]; abel
    · rw [← h2]; simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]; abel
  refine ⟨_, hG, fun g hg s => ?_⟩
  have hM := sumBd_isUpq_mul hg hG
  have hM12 : (g * fromBlocks S1 (Z * S2) (Zᴴ * S1) S2).toBlocks₁₂ =
      (g.toBlocks₁₁ * Z + g.toBlocks₁₂) * S2 := by
    conv_lhs => rw [← fromBlocks_toBlocks g]
    rw [fromBlocks_multiply, toBlocks_fromBlocks₁₂]; simp only [Matrix.add_mul, Matrix.mul_assoc]
  have hM22 : (g * fromBlocks S1 (Z * S2) (Zᴴ * S1) S2).toBlocks₂₂ =
      (g.toBlocks₂₁ * Z + g.toBlocks₂₂) * S2 := by
    conv_lhs => rw [← fromBlocks_toBlocks g]
    rw [fromBlocks_multiply, toBlocks_fromBlocks₂₂]; simp only [Matrix.add_mul, Matrix.mul_assoc]
  have hW : mob g Z = (g * fromBlocks S1 (Z * S2) (Zᴴ * S1) S2).toBlocks₁₂ *
      ((g * fromBlocks S1 (Z * S2) (Zᴴ * S1) S2).toBlocks₂₂)⁻¹ := by
    rw [hM12, hM22, Matrix.mul_inv_rev, mob]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc S2, hS2i, Matrix.one_mul]
  rw [dpow, hW, (sumBd_weight hM).2]

end

end ReciprocityTheory.ChartRestriction.G.AR.Up
