import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelGramPosSemidef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareMetricPuncturedPolydiscBounds

set_option autoImplicit false

noncomputable section

open Complex Metric Matrix GlobalTheory.HermFrame
open scoped ComplexOrder

namespace GlobalTheory.CurvInterp

theorem norm_deriv_le_of_norm_lt_one {f : ℂ → ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hf : DifferentiableOn ℂ f (ball 0 δ)) (h1 : ∀ ζ ∈ ball (0 : ℂ) δ, ‖f ζ‖ < 1) :
    ‖deriv f 0‖ ≤ 2 / δ := by
  refine Complex.norm_deriv_le_div_of_mapsTo_ball hf (fun ζ hζ => ?_) hδ
  rw [mem_closedBall, dist_eq_norm]
  have h0 := h1 0 (mem_ball_self hδ)
  calc ‖f ζ - f 0‖ ≤ ‖f ζ‖ + ‖f 0‖ := norm_sub_le _ _
    _ ≤ 2 := by linarith [h1 ζ hζ]

theorem norm_deriv_le_of_punctured {f : ℂ → ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hf : DifferentiableOn ℂ f (ball 0 δ)) (hne : ∀ ζ ∈ ball (0 : ℂ) δ, f ζ ≠ 0)
    (h1 : ∀ ζ ∈ ball (0 : ℂ) δ, ‖f ζ‖ < 1) :
    ‖deriv f 0‖ ≤ 4 * (-Real.log ‖f 0‖) * ‖f 0‖ / δ := by
  have hd : DifferentiableOn ℂ (fun z => deriv f z / f z) (ball 0 δ) :=
    (hf.deriv isOpen_ball).div hf hne
  obtain ⟨g, hg0, hg⟩ := hd.isExactOn_ball.with_val_at (0 : ℂ) 0
  have h00 : (0 : ℂ) ∈ ball (0 : ℂ) δ := mem_ball_self hδ
  have hf0 : f 0 ≠ 0 := hne 0 h00
  have hfd : ∀ z ∈ ball (0 : ℂ) δ, HasDerivAt f (deriv f z) z := fun z hz =>
    ((hf z hz).differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
  have hexp : ∀ z ∈ ball (0 : ℂ) δ, f z = f 0 * Complex.exp (g z) := by
    intro z hz
    have hh : ∀ z ∈ ball (0 : ℂ) δ, HasDerivAt (fun w => f w * Complex.exp (-g w)) 0 z := by
      intro z hz
      have h1 : HasDerivAt (fun w => f w * Complex.exp (-g w))
          (deriv f z * Complex.exp (-g z) + f z * (Complex.exp (-g z) * -(deriv f z / f z))) z :=
        (hfd z hz).mul ((hg z hz).neg.cexp)
      refine h1.congr_deriv ?_
      have e : f z * (deriv f z / f z) = deriv f z := mul_div_cancel₀ _ (hne z hz)
      linear_combination (-Complex.exp (-g z)) * e
    have hconst := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0 : ℂ) δ).isPreconnected
      (fun z hz => (hh z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => by simpa using (hh z hz).deriv) hz h00
    simp only [hg0, neg_zero, Complex.exp_zero, mul_one] at hconst
    rw [← hconst, mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
  have hp : 0 < ‖f 0‖ := norm_pos_iff.2 hf0
  set A := -Real.log ‖f 0‖ with hAdef
  have hA : 0 < A := neg_pos.2 (Real.log_neg hp (h1 0 h00))
  have hre : Set.MapsTo g (ball 0 δ) {u | u.re ≤ A} := by
    intro u hu
    have h2 := h1 u hu
    rw [hexp u hu, norm_mul, Complex.norm_exp] at h2
    have h3 := Real.log_neg (by positivity) h2
    rw [Real.log_mul hp.ne' (Real.exp_pos _).ne', Real.log_exp] at h3
    show (g u).re ≤ A
    linarith
  have hgd : DifferentiableOn ℂ g (ball 0 δ) := fun u hu => (hg u hu).differentiableAt.differentiableWithinAt
  have hsph : ∀ u ∈ sphere (0 : ℂ) (δ / 2), ‖g u‖ ≤ 2 * A := by
    intro u hu
    have hn : ‖u‖ = δ / 2 := by simpa using hu
    have hu' : u ∈ ball (0 : ℂ) δ := by rw [mem_ball_zero_iff, hn]; linarith
    have hBC := Complex.borelCaratheodory_zero hA hgd hre hδ hu' hg0
    rw [hn] at hBC
    calc ‖g u‖ ≤ 2 * A * (δ / 2) / (δ - δ / 2) := hBC
      _ = 2 * A := by field_simp; ring
  have hdc : DiffContOnCl ℂ g (ball 0 (δ / 2)) :=
    hgd.diffContOnCl_ball (closedBall_subset_ball (by linarith))
  have hC := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity : 0 < δ / 2) hdc hsph
  rw [(hg 0 h00).deriv, norm_div] at hC
  rw [div_le_iff₀ hp] at hC
  calc ‖deriv f 0‖ ≤ 2 * A / (δ / 2) * ‖f 0‖ := hC
    _ = 4 * A * ‖f 0‖ / δ := by field_simp; ring

end GlobalTheory.CurvInterp

namespace GlobalTheory.CurvInterp

theorem modelGram_term_le {e m : ℕ} (σ : Fin m → Option (Fin e)) (z w : Fin e → ℂ) (j : Fin e) :
    (modelGram σ z j j).re * ‖w j‖ ^ 2 ≤ gnorm (modelGram σ z) w ^ 2 := by
  rw [gnorm_sq (modelGram_posSemidef σ z), form_modelGram σ z w, GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms.modelAt]
  have hle := Finset.single_le_sum (s := Finset.univ) (a := j)
    (f := fun k => (modelGram σ z k k).re * ‖w k‖ ^ 2) (fun k _ => by
      simp only [modelGram, diagonal_apply_eq, ofReal_re]
      split_ifs <;> positivity) (Finset.mem_univ j)
  refine hle.trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_))
  simp only [modelGram, diagonal_apply_eq, ofReal_re]
  split_ifs <;> ring

end GlobalTheory.CurvInterp

namespace GlobalTheory.CurvInterp

open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.PoincareBounds

theorem schwarz_punct : ∀ (e m n k : ℕ) (hk : k ≤ n) (σ : Fin m → Option (Fin e)) (ρ : ℝ)
    (φ : (Fin e → ℂ) → Fin n → ℂ), 0 < ρ → DifferentiableOn ℂ φ (Metric.ball 0 ρ) →
    (∀ z ∈ Metric.ball (0 : Fin e → ℂ) ρ, φ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.polydisc n 1) →
    (∀ z ∈ punct σ ρ, φ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.punctured hk 1) →
    ∃ ρ' C : ℝ, 0 < ρ' ∧ ρ' ≤ ρ ∧ ∀ z ∈ punct σ ρ', ∀ w,
      GlobalTheory.HermFrame.gnorm (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.poincareGram k (φ z)) (fderiv ℂ φ z w) ≤
        C * GlobalTheory.HermFrame.gnorm (modelGram σ z) w := by
  intro e m n k hk σ ρ φ hρ hφd hφD hφP
  classical
  set ρ₀ := min ρ 1 with hρ₀
  have hρ₀pos : 0 < ρ₀ := lt_min hρ one_pos
  have hρ₀1 : ρ₀ ≤ 1 := min_le_right _ _
  have hρ₀ρ : ρ₀ ≤ ρ := min_le_left _ _
  set δ₀ := min Real.pi (ρ₀ / 2) with hδ₀
  have hδ₀pos : 0 < δ₀ := lt_min Real.pi_pos (by positivity)
  have hδ₀pi : δ₀ ≤ Real.pi := min_le_left _ _
  have hδ₀ρ : δ₀ ≤ ρ₀ / 2 := min_le_right _ _
  have hρ'ρ₀ : ρ₀ ^ 2 / 2 ≤ ρ₀ / 2 := by nlinarith
  refine ⟨ρ₀ ^ 2 / 2, (n + 1) * (8 * Real.pi / δ₀), by positivity, by linarith, ?_⟩
  intro z hz w
  have hzρ : ‖z‖ < ρ₀ ^ 2 / 2 := mem_ball_zero_iff.1 hz.1
  have hzj : ∀ j, ‖z j‖ < ρ₀ ^ 2 / 2 := fun j => (norm_le_pi_norm z j).trans_lt hzρ
  have hzj1 : ∀ j, ‖z j‖ < 1 := fun j => by linarith [hzj j]
  set M := gnorm (modelGram σ z) w with hMdef
  have hM0 : 0 ≤ M := gnorm_nonneg _ _

  have hbr : ∀ j, (∃ i, σ i = some j) → z j ≠ 0 := fun j ⟨i, hi⟩ => hz.2 i j hi
  have hwb : ∀ j, (∃ i, σ i = some j) → ‖w j‖ ≤ M * (‖z j‖ * tlog (z j)) := by
    intro j hj
    have h := modelGram_term_le σ z w j
    simp only [modelGram, diagonal_apply_eq, ofReal_re, if_pos hj] at h
    obtain ⟨hp, -⟩ := norm_mul_tlog_lt (hbr j hj) (hzj1 j)
    have e1 : ‖z j‖ ^ 2 * GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms.tOf (z j) ^ 2 = (‖z j‖ * tlog (z j)) ^ 2 := by
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms.tOf, tlog]; ring
    rw [e1, one_div, inv_mul_eq_div, div_le_iff₀ (by positivity), ← mul_pow] at h
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h
  have hwM : ∀ j, ‖w j‖ ≤ M := by
    intro j
    by_cases hj : ∃ i, σ i = some j
    · obtain ⟨hp, hl⟩ := norm_mul_tlog_lt (hbr j hj) (hzj1 j)
      nlinarith [hwb j hj]
    · have h := modelGram_term_le σ z w j
      simp only [modelGram, diagonal_apply_eq, ofReal_re, if_neg hj, one_mul] at h
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) hM0 two_ne_zero).1 h
  rcases hM0.eq_or_lt with hM | hMpos
  · have hw : w = 0 := funext fun j => norm_le_zero_iff.1 (by rw [hM]; exact hwM j)
    subst hw
    simp only [map_zero, gnorm_zero]
    exact mul_nonneg (by positivity) hM0

  set δ := δ₀ / M with hδdef
  have hδ : 0 < δ := div_pos hδ₀pos hMpos
  have hδM : δ * M = δ₀ := div_mul_cancel₀ _ hMpos.ne'
  let γ : ℂ → Fin e → ℂ := fun ζ j =>
    if ∃ i, σ i = some j then z j * Complex.exp (ζ * (w j / z j)) else z j + ζ * w j
  have hγ0 : γ 0 = z := by
    funext j; by_cases hj : ∃ i, σ i = some j <;> simp [γ, hj]
  have hγd : HasDerivAt γ w 0 := by
    refine hasDerivAt_pi.2 fun j => ?_
    by_cases hj : ∃ i, σ i = some j
    · simp only [γ, if_pos hj]
      have h : HasDerivAt (fun ζ : ℂ => z j * Complex.exp (ζ * (w j / z j)))
          (z j * (Complex.exp (0 * (w j / z j)) * (w j / z j))) 0 :=
        ((hasDerivAt_mul_const (w j / z j)).cexp).const_mul (z j)
      refine h.congr_deriv ?_
      rw [zero_mul, Complex.exp_zero, one_mul, mul_div_cancel₀ _ (hbr j hj)]
    · simp only [γ, if_neg hj]
      exact (hasDerivAt_mul_const (w j)).const_add (z j)
  have hγdiff : Differentiable ℂ γ := by
    refine differentiable_pi.2 fun j => ?_
    by_cases hj : ∃ i, σ i = some j
    · simp only [γ, if_pos hj]; fun_prop
    · simp only [γ, if_neg hj]; fun_prop
  have hγmem : ∀ ζ ∈ ball (0 : ℂ) δ, γ ζ ∈ punct σ ρ := by
    intro ζ hζ
    have hζ' : ‖ζ‖ < δ := mem_ball_zero_iff.1 hζ
    have hcoord : ∀ j, ‖γ ζ j‖ < ρ₀ := by
      intro j
      by_cases hj : ∃ i, σ i = some j
      · simp only [γ, if_pos hj]
        have hz0 := hbr j hj
        have hzp : 0 < ‖z j‖ := norm_pos_iff.2 hz0
        have ht := tlog_pos hz0 (hzj1 j)
        set x := (ζ * (w j / z j)).re with hx
        have hx1 : x ≤ ‖ζ‖ * (‖w j‖ / ‖z j‖) := by
          rw [hx]; exact (re_le_norm _).trans (by rw [norm_mul, norm_div])
        have hx2 : ‖ζ‖ * (‖w j‖ / ‖z j‖) ≤ ‖ζ‖ * (M * tlog (z j)) := by
          gcongr
          rw [div_le_iff₀ hzp]; nlinarith [hwb j hj]
        have hx3 : ‖ζ‖ * (M * tlog (z j)) < δ * (M * tlog (z j)) := by
          gcongr
        have hx4 : δ * (M * tlog (z j)) ≤ Real.pi * tlog (z j) := by
          rw [← mul_assoc, hδM]; gcongr
        have hx5 : Real.pi * tlog (z j) = -Real.log ‖z j‖ / 2 := by
          simp only [tlog]; field_simp
        have hxl : 2 * x < -Real.log ‖z j‖ := by linarith
        have he : Real.exp (2 * x) < ‖z j‖⁻¹ := by
          calc Real.exp (2 * x) < Real.exp (-Real.log ‖z j‖) := Real.exp_lt_exp.2 hxl
            _ = ‖z j‖⁻¹ := by rw [Real.exp_neg, Real.exp_log hzp]
        have hsq : (‖z j‖ * Real.exp x) ^ 2 < ρ₀ ^ 2 := by
          have e2 : Real.exp x ^ 2 = Real.exp (2 * x) := by
            rw [← Real.exp_nat_mul]; norm_num
          calc (‖z j‖ * Real.exp x) ^ 2 = ‖z j‖ ^ 2 * Real.exp (2 * x) := by rw [mul_pow, e2]
            _ < ‖z j‖ ^ 2 * ‖z j‖⁻¹ := by gcongr
            _ = ‖z j‖ := by field_simp
            _ < ρ₀ ^ 2 := by nlinarith [hzj j]
        rw [norm_mul, Complex.norm_exp]
        exact (pow_lt_pow_iff_left₀ (by positivity) hρ₀pos.le two_ne_zero).1 hsq
      · simp only [γ, if_neg hj]
        calc ‖z j + ζ * w j‖ ≤ ‖z j‖ + ‖ζ‖ * ‖w j‖ := by
              rw [← norm_mul]; exact norm_add_le _ _
          _ ≤ ‖z j‖ + δ * M := by
              gcongr
              exact hwM j
          _ < ρ₀ := by rw [hδM]; linarith [hzj j]
    refine ⟨mem_ball_zero_iff.2 ((pi_norm_lt_iff (by linarith)).2 fun j => (hcoord j).trans_le hρ₀ρ),
      fun i j hi => ?_⟩
    have hj : ∃ i', σ i' = some j := ⟨i, hi⟩
    simp only [γ, if_pos hj]
    exact mul_ne_zero (hbr j ⟨i, hi⟩) (Complex.exp_ne_zero _)

  have hρ'ρ : ρ₀ ^ 2 / 2 ≤ ρ := by linarith
  have hzB : z ∈ ball (0 : Fin e → ℂ) ρ := punct_mono σ hρ'ρ hz |>.1
  have hzP : φ z ∈ punctured hk 1 := hφP z (punct_mono σ hρ'ρ hz)
  have hφz : DifferentiableAt ℂ φ z := (hφd z hzB).differentiableAt (isOpen_ball.mem_nhds hzB)
  have hcomp : HasDerivAt (fun ζ => φ (γ ζ)) (fderiv ℂ φ z w) 0 := by
    have h : HasFDerivAt φ (fderiv ℂ φ z) (γ 0) := by rw [hγ0]; exact hφz.hasFDerivAt
    exact h.comp_hasDerivAt 0 hγd
  have hmaps : Set.MapsTo γ (ball 0 δ) (ball 0 ρ) := fun ζ hζ => (hγmem ζ hζ).1
  have hFd : ∀ i, DifferentiableOn ℂ (fun ζ => φ (γ ζ) i) (ball 0 δ) := fun i =>
    differentiableOn_pi.1 (hφd.comp hγdiff.differentiableOn hmaps) i
  have hF1 : ∀ i, ∀ ζ ∈ ball (0 : ℂ) δ, ‖φ (γ ζ) i‖ < 1 := fun i ζ hζ => hφD _ (hmaps hζ) i
  have hder : ∀ i, deriv (fun ζ => φ (γ ζ) i) 0 = fderiv ℂ φ z w i := fun i =>
    (hasDerivAt_pi.1 hcomp i).deriv
  have hF0 : ∀ i, φ (γ 0) i = φ z i := fun i => by rw [hγ0]
  set v := fderiv ℂ φ z w with hv
  have hδinv : 1 / δ = M / δ₀ := by rw [hδdef]; field_simp
  set K := 8 * Real.pi / δ₀ * M with hK
  have hK0 : 0 ≤ K := by positivity
  have hvall : ∀ i, ‖v i‖ ≤ K := by
    intro i
    have h := norm_deriv_le_of_norm_lt_one hδ (hFd i) (hF1 i)
    rw [hder i] at h
    calc ‖v i‖ ≤ 2 / δ := h
      _ = 2 * (M / δ₀) := by rw [← hδinv]; ring
      _ ≤ K := by
        rw [hK, mul_div_assoc', div_mul_eq_mul_div]
        gcongr
        · linarith [Real.pi_gt_three]
  have hvbr : ∀ i : Fin n, i.val < k → ‖v i‖ ≤ K * (‖φ z i‖ * tlog (φ z i)) := by
    intro i hi
    have hne : ∀ ζ ∈ ball (0 : ℂ) δ, φ (γ ζ) i ≠ 0 := fun ζ hζ =>
      (hφP _ (hγmem ζ hζ)).2 ⟨i.val, hi⟩
    have h := norm_deriv_le_of_punctured hδ (hFd i) hne (hF1 i)
    rw [hder i, hF0 i] at h
    have hl : -Real.log ‖φ z i‖ = 2 * Real.pi * tlog (φ z i) := by
      simp only [tlog]; field_simp
    calc ‖v i‖ ≤ 4 * (-Real.log ‖φ z i‖) * ‖φ z i‖ / δ := h
      _ = K * (‖φ z i‖ * tlog (φ z i)) := by
        rw [hl, div_eq_mul_one_div, hδinv, hK]; field_simp; ring

  have hterm : ∀ i, pdiag k (φ z) i * ‖v i‖ ^ 2 ≤ K ^ 2 := by
    intro i
    unfold pdiag
    split_ifs with hi
    · have hp0 : φ z i ≠ 0 := hzP.2 ⟨i.val, hi⟩
      obtain ⟨hp, -⟩ := norm_mul_tlog_lt hp0 (hzP.1 i)
      have h := hvbr i hi
      have h2 : ‖v i‖ ^ 2 ≤ (K * (‖φ z i‖ * tlog (φ z i))) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h 2
      have e1 : ‖φ z i‖ ^ 2 * tlog (φ z i) ^ 2 = (‖φ z i‖ * tlog (φ z i)) ^ 2 := by ring
      rw [e1, one_div_mul_eq_div, div_le_iff₀ (by positivity)]
      nlinarith [sq_nonneg K, sq_nonneg (‖φ z i‖ * tlog (φ z i))]
    · have h2 : ‖v i‖ ^ 2 ≤ K ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hvall i) 2
      nlinarith
  have hsum : gnorm (poincareGram k (φ z)) v ^ 2 ≤ ((n + 1) * K) ^ 2 := by
    rw [poincareGram_eq, gnorm_diag_sq _ (pdiag_nonneg k (φ z))]
    calc ∑ i, pdiag k (φ z) i * ‖v i‖ ^ 2 ≤ ∑ _i : Fin n, K ^ 2 := Finset.sum_le_sum fun i _ => hterm i
      _ = n * K ^ 2 := by simp
      _ ≤ ((n + 1) * K) ^ 2 := by
        have : (n : ℝ) ≤ (n + 1) ^ 2 := by nlinarith
        nlinarith [sq_nonneg K]
  have hfin := (pow_le_pow_iff_left₀ (gnorm_nonneg _ _) (by positivity) two_ne_zero).1 hsum
  calc gnorm (poincareGram k (φ z)) v ≤ (n + 1) * K := hfin
    _ = (n + 1) * (8 * Real.pi / δ₀) * M := by rw [hK]; ring

end GlobalTheory.CurvInterp
