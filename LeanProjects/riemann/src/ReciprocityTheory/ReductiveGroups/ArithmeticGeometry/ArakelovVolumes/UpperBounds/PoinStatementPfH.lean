import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PoinStatementPfG

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
open scoped ENNReal Matrix ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem det_near_one (n : ℕ) : ∃ η > 0, ∀ A : Matrix (Fin n) (Fin n) ℂ,
    (∀ i j, ‖A i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j‖ < η) → 1 / 2 ≤ ‖A.det‖ := by
  set g : (Fin n → Fin n → ℂ) → ℂ :=
    fun A => ∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ • ∏ i, A (σ i) i with hg
  have hgc : Continuous g := by rw [hg]; fun_prop
  have hgdet : ∀ A : Matrix (Fin n) (Fin n) ℂ, A.det = g A := fun A => Matrix.det_apply A
  set I : Fin n → Fin n → ℂ := (1 : Matrix (Fin n) (Fin n) ℂ) with hI
  have hgI : g I = 1 := by rw [← hgdet]; exact Matrix.det_one
  obtain ⟨η, hη, h⟩ := Metric.continuousAt_iff.1 hgc.continuousAt (1 / 2 : ℝ) (by norm_num)
  refine ⟨η, hη, fun A hA => ?_⟩
  have hd : dist (Matrix.of.symm A) I < η :=
    (dist_pi_lt_iff hη).2 fun i => (dist_pi_lt_iff hη).2 fun j => by rw [dist_eq_norm]; exact hA i j
  have h2 := h hd
  have h4 : g (Matrix.of.symm A) = A.det := (hgdet A).symm
  rw [hgI, h4, dist_eq_norm] at h2
  have h3 := norm_sub_norm_le (1 : ℂ) A.det
  rw [norm_sub_rev, norm_one] at h3
  linarith

theorem diag_re {m n : Type*} [Fintype n] (C : Matrix m n ℂ) (i : m) :
    ((C * Cᴴ) i i).re = ∑ j, Complex.normSq (C i j) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show star (C i j) = (starRingEnd ℂ) (C i j) from rfl, Complex.mul_conj, Complex.ofReal_re]

theorem Kc_entry {p q : ℕ} {M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (h : IsUpq M) (i : Fin q)
    (j : Fin p) : ‖((M.toBlocks₂₂)⁻¹ * M.toBlocks₂₁) i j‖ ≤ 1 := by
  set A := M.toBlocks₂₂ with hA
  set B := M.toBlocks₂₁ with hB
  have hAB : A * Aᴴ = 1 + B * Bᴴ := (sumBdIsUpq_blocks h).2.2.2
  have hU : IsUnit A.det := isUnit_iff_ne_zero.2 (sumBd_weight h).1
  have hK : (A⁻¹ * B) * (A⁻¹ * B)ᴴ = 1 - A⁻¹ * (A⁻¹)ᴴ := by
    have e1 : B * Bᴴ = A * Aᴴ - 1 := by rw [hAB]; abel
    have e2 : Aᴴ * (A⁻¹)ᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, Matrix.nonsing_inv_mul _ hU, Matrix.conjTranspose_one]
    calc (A⁻¹ * B) * (A⁻¹ * B)ᴴ = A⁻¹ * (B * Bᴴ) * (A⁻¹)ᴴ := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = A⁻¹ * A * (Aᴴ * (A⁻¹)ᴴ) - A⁻¹ * (A⁻¹)ᴴ := by
          rw [e1, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = 1 - A⁻¹ * (A⁻¹)ᴴ := by rw [e2, Matrix.nonsing_inv_mul _ hU, Matrix.mul_one]
  have hdiag := congrArg (fun C => (C i i).re) hK
  rw [diag_re, Matrix.sub_apply, Complex.sub_re, diag_re, Matrix.one_apply_eq, Complex.one_re] at hdiag
  have hnn : 0 ≤ ∑ l, Complex.normSq ((A⁻¹) i l) := Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  have hle : Complex.normSq ((A⁻¹ * B) i j) ≤ ∑ l, Complex.normSq ((A⁻¹ * B) i l) :=
    Finset.single_le_sum (f := fun l => Complex.normSq ((A⁻¹ * B) i l))
      (fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ j)
  have h1 : ‖(A⁻¹ * B) i j‖ ^ 2 ≤ 1 := by rw [← Complex.normSq_eq_norm_sq]; linarith
  nlinarith [norm_nonneg ((A⁻¹ * B) i j)]

theorem toBlocks_lowerRight_mul {α β : Type*} [Fintype α] [Fintype β] (M N : Matrix (α ⊕ β) (α ⊕ β) ℂ) :
    (M * N).toBlocks₂₂ = M.toBlocks₂₁ * N.toBlocks₁₂ + M.toBlocks₂₂ * N.toBlocks₂₂ := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks M, ← Matrix.fromBlocks_toBlocks N]
  rw [Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₂₂]

theorem det_split {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] (M N : Matrix (α ⊕ β) (α ⊕ β) ℂ)
    (hM : M.toBlocks₂₂.det ≠ 0) :
    (M * N).toBlocks₂₂.det =
      M.toBlocks₂₂.det * ((M.toBlocks₂₂)⁻¹ * M.toBlocks₂₁ * N.toBlocks₁₂ + N.toBlocks₂₂).det := by
  rw [toBlocks_lowerRight_mul, ← Matrix.det_mul, Matrix.mul_add]
  congr 2
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hM),
    Matrix.one_mul]

theorem nmat_entry (X : Data E r) (w : V (nd X)) (τ : X.Ψ) (a b : Fin r) :
    ‖mat (nmat X w) τ a b - (1 : Matrix (Fin r) (Fin r) ℂ) a b‖ ≤ ‖w‖ := by
  simp only [mat, nmat, Matrix.of_apply, Matrix.one_apply]
  by_cases h : b < a
  · rw [dif_pos h, if_neg (ne_of_lt h).symm, sub_zero]
    exact PiLp.norm_apply_le w _
  · rw [dif_neg h]
    split_ifs <;> simp

theorem Mq_cpt (X : Data E r) (x0 x : Frame X.Ψ r) (w : V (nd X)) (τ : X.Ψ) :
    Mq X x0 (cpt X x w) τ =
      Mq X x0 x τ * ((mat (nmat X w) τ).map (starRingEnd ℂ)).submatrix (eS X) (eS X) := by
  unfold Mq
  rw [show cpt X x w = rmul x (nmat X w) from rfl, gM_rmul, Matrix.map_mul,
    ← Matrix.submatrix_mul_equiv _ _ _ (eS X) _]

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
open scoped ENNReal Matrix ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def Nw (X : Data E r) (w : V (nd X)) (τ : X.Ψ) :
    Matrix (Fin (r - X.p0) ⊕ Fin X.p0) (Fin (r - X.p0) ⊕ Fin X.p0) ℂ :=
  ((mat (nmat X w) τ).map (starRingEnd ℂ)).submatrix (eS X) (eS X)

theorem Mq_cpt' (X : Data E r) (x0 x : Frame X.Ψ r) (w : V (nd X)) (τ : X.Ψ) :
    Mq X x0 (cpt X x w) τ = Mq X x0 x τ * Nw X w τ := Mq_cpt X x0 x w τ

theorem N_entries (X : Data E r) (w : V (nd X)) (τ : X.Ψ) (u v : Fin (r - X.p0) ⊕ Fin X.p0) :
    ‖Nw X w τ u v - (1 : Matrix (Fin (r - X.p0) ⊕ Fin X.p0) (Fin (r - X.p0) ⊕ Fin X.p0) ℂ) u v‖ ≤ ‖w‖ := by
  have h1 : (1 : Matrix (Fin (r - X.p0) ⊕ Fin X.p0) (Fin (r - X.p0) ⊕ Fin X.p0) ℂ) u v =
      starRingEnd ℂ ((1 : Matrix (Fin r) (Fin r) ℂ) (eS X u) (eS X v)) := by
    simp [Matrix.one_apply, apply_ite]
  rw [Nw, Matrix.submatrix_apply, Matrix.map_apply, h1, ← map_sub, Complex.norm_conj]
  exact nmat_entry X w τ _ _

theorem pert_entry (X : Data E r) {x0 x : Frame X.Ψ r} (hx0 : IsOrth X x0) (hx : IsOrth X x)
    (w : V (nd X)) (τ : X.Ψ) (i j : Fin X.p0) :
    ‖(((Mq X x0 x τ).toBlocks₂₂)⁻¹ * (Mq X x0 x τ).toBlocks₂₁ * (Nw X w τ).toBlocks₁₂ +
      (Nw X w τ).toBlocks₂₂) i j - (1 : Matrix (Fin X.p0) (Fin X.p0) ℂ) i j‖ ≤ ((r : ℝ) + 1) * ‖w‖ := by
  set K := ((Mq X x0 x τ).toBlocks₂₂)⁻¹ * (Mq X x0 x τ).toBlocks₂₁ with hKdef
  have hK : ∀ i l, ‖K i l‖ ≤ 1 := fun i l => Kc_entry (Mq_isUpq X hx0 hx τ) i l
  have hN12 : ∀ l j, ‖(Nw X w τ).toBlocks₁₂ l j‖ ≤ ‖w‖ := fun l j => by
    have := N_entries X w τ (Sum.inl l) (Sum.inr j)
    simpa [Matrix.toBlocks₁₂, Matrix.one_apply] using this
  have hN22 : ‖(Nw X w τ).toBlocks₂₂ i j - (1 : Matrix (Fin X.p0) (Fin X.p0) ℂ) i j‖ ≤ ‖w‖ := by
    have := N_entries X w τ (Sum.inr i) (Sum.inr j)
    simpa [Matrix.toBlocks₂₂, Matrix.one_apply] using this
  rw [Matrix.add_apply, add_sub_assoc, Matrix.mul_apply]
  have hr : ((r - X.p0 : ℕ) : ℝ) ≤ r := by exact_mod_cast Nat.sub_le r X.p0
  calc ‖∑ l, K i l * (Nw X w τ).toBlocks₁₂ l j +
        ((Nw X w τ).toBlocks₂₂ i j - (1 : Matrix (Fin X.p0) (Fin X.p0) ℂ) i j)‖
      ≤ ‖∑ l, K i l * (Nw X w τ).toBlocks₁₂ l j‖ +
          ‖(Nw X w τ).toBlocks₂₂ i j - (1 : Matrix (Fin X.p0) (Fin X.p0) ℂ) i j‖ := norm_add_le _ _
    _ ≤ ∑ _l : Fin (r - X.p0), ‖w‖ + ‖w‖ := by
        refine add_le_add ((norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)) hN22
        rw [norm_mul]
        calc ‖K i l‖ * ‖(Nw X w τ).toBlocks₁₂ l j‖ ≤ 1 * ‖w‖ :=
              mul_le_mul (hK i l) (hN12 l j) (norm_nonneg _) zero_le_one
          _ = ‖w‖ := one_mul _
    _ ≤ ((r : ℝ) + 1) * ‖w‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        nlinarith [norm_nonneg w]

theorem ka_comp (X : Data E r) {x0 : Frame X.Ψ r} (hx0 : IsOrth X x0) {bb : ℝ} (hbb : 0 ≤ bb) :
    ∃ ρ1 > 0, ∀ x, IsOrth X x → ∀ w : V (nd X), ‖w‖ < ρ1 →
      kaY X x0 bb (cpt X x w) ≤ Real.exp (bb * (3 * X.Ψ.card * Real.log 2)) * kaY X x0 bb x := by
  obtain ⟨η, hη, hdet⟩ := det_near_one X.p0
  have e1 : ∀ᶠ w in 𝓝 (0 : V (nd X)), ∀ τ, ‖lminor (Gw X w τ) (i0 X)‖ < 2 := by
    rw [Filter.eventually_all]; intro τ
    exact (cont_lminor X τ (i0 X)).norm.continuousAt.eventually_lt continuousAt_const
      (by rw [norm_lminor_zero]; norm_num)
  obtain ⟨R1, hR1, hR1b⟩ := Metric.eventually_nhds_iff_ball.1 e1
  refine ⟨min R1 (η / ((r : ℝ) + 1)), lt_min hR1 (by positivity), fun x hx w hw => ?_⟩
  have hwR : w ∈ Metric.ball (0 : V (nd X)) R1 :=
    mem_ball_zero_iff.2 (lt_of_lt_of_le hw (min_le_left _ _))
  have hwη : ((r : ℝ) + 1) * ‖w‖ < η := by
    have := lt_of_lt_of_le hw (min_le_right _ _)
    rwa [lt_div_iff₀ (by positivity), mul_comm] at this
  have hterm : ∀ τ, Real.log ‖dmin X.Gm (cpt X x w) τ (i0 X)‖ -
      2 * Real.log ‖lminor (gM X x0 (cpt X x w) τ) (i0 X)‖ ≤
        3 * Real.log 2 - 2 * Real.log ‖lminor (gM X x0 x τ) (i0 X)‖ := by
    intro τ
    have hA : Real.log ‖dmin X.Gm (cpt X x w) τ (i0 X)‖ ≤ Real.log 2 := by
      rw [dmin_cpt_orth X hx]
      rcases eq_or_lt_of_le (norm_nonneg (lminor (Gw X w τ) (i0 X))) with h0 | h0
      · rw [← h0, Real.log_zero]; exact (Real.log_pos (by norm_num)).le
      · exact Real.log_le_log h0 (hR1b w hwR τ).le
    have hM22 := (sumBd_weight (Mq_isUpq X hx0 hx τ)).1
    have hnorm : ∀ y, ‖lminor (gM X x0 y τ) (i0 X)‖ = ‖(Mq X x0 y τ).toBlocks₂₂.det‖ := fun y => by
      rw [det_lowerBlock_eq_conj_minor, Complex.norm_conj]; rfl
    have hP : 1 / 2 ≤ ‖(((Mq X x0 x τ).toBlocks₂₂)⁻¹ * (Mq X x0 x τ).toBlocks₂₁ *
        (Nw X w τ).toBlocks₁₂ + (Nw X w τ).toBlocks₂₂).det‖ :=
      hdet _ (fun i j => lt_of_le_of_lt (pert_entry X hx0 hx w τ i j) hwη)
    have hpos : 0 < ‖(Mq X x0 x τ).toBlocks₂₂.det‖ := norm_pos_iff.2 hM22
    have hB : Real.log ‖lminor (gM X x0 x τ) (i0 X)‖ - Real.log 2 ≤
        Real.log ‖lminor (gM X x0 (cpt X x w) τ) (i0 X)‖ := by
      rw [hnorm, hnorm, Mq_cpt', det_split _ _ hM22, norm_mul,
        Real.log_mul hpos.ne' (by linarith)]
      have h2 : Real.log (1 / 2) ≤ Real.log ‖(((Mq X x0 x τ).toBlocks₂₂)⁻¹ * (Mq X x0 x τ).toBlocks₂₁ *
          (Nw X w τ).toBlocks₁₂ + (Nw X w τ).toBlocks₂₂).det‖ := Real.log_le_log (by norm_num) hP
      rw [one_div, Real.log_inv] at h2
      linarith
    linarith
  have hrh : rhY X x0 x - 3 * X.Ψ.card * Real.log 2 ≤ rhY X x0 (cpt X x w) := by
    unfold rhY
    simp only [norm_dmin_orth' X hx, Real.log_one, zero_sub]
    have hs : ∑ τ, (Real.log ‖dmin X.Gm (cpt X x w) τ (i0 X)‖ -
        2 * Real.log ‖lminor (gM X x0 (cpt X x w) τ) (i0 X)‖) ≤
          ∑ τ, (3 * Real.log 2 - 2 * Real.log ‖lminor (gM X x0 x τ) (i0 X)‖) :=
      Finset.sum_le_sum fun τ _ => hterm τ
    have e2 : ∑ τ : X.Ψ, (3 * Real.log 2 - 2 * Real.log ‖lminor (gM X x0 x τ) (i0 X)‖) =
        (X.Ψ.card : ℝ) * (3 * Real.log 2) - ∑ τ, 2 * Real.log ‖lminor (gM X x0 x τ) (i0 X)‖ := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
    rw [Finset.sum_neg_distrib]
    linarith
  unfold kaY
  calc Real.exp (-bb * rhY X x0 (cpt X x w))
      ≤ Real.exp (-bb * (rhY X x0 x - 3 * X.Ψ.card * Real.log 2)) := by
        refine Real.exp_le_exp.2 ?_
        have := mul_le_mul_of_nonneg_left hrh hbb
        linarith
    _ = Real.exp (bb * (3 * X.Ψ.card * Real.log 2)) * Real.exp (-bb * rhY X x0 x) := by
        rw [← Real.exp_add]; congr 1; ring

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
