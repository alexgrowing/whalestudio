import Mathlib
import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralExpNegHermitianFormPosDefStatement
open Filter Topology MeasureTheory Metric ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder

namespace GlobalTheory.TruncGauss

noncomputable def qf {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (w : V n) : ℂ :=
  ∑ j, ∑ l, A j l * w j * (starRingEnd ℂ) (w l)

theorem qf_add {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (w : V n) :
    qf (A + B) w = qf A w + qf B w := by
  simp only [qf, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

theorem qf_smul {n : ℕ} (c : ℂ) (A : Matrix (Fin n) (Fin n) ℂ) (w : V n) :
    qf (c • A) w = c * qf A w := by
  simp only [qf, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem qf_one {n : ℕ} (w : V n) : qf (1 : Matrix (Fin n) (Fin n) ℂ) w = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [qf, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring

theorem qf_re_nonneg {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosSemidef) (w : V n) :
    0 ≤ (qf H w).re := by
  have h := hH.dotProduct_mulVec_nonneg (fun j => (starRingEnd ℂ) (w j))
  have e : star (fun j => (starRingEnd ℂ) (w j)) ⬝ᵥ (H.mulVec (fun j => (starRingEnd ℂ) (w j))) = qf H w := by
    simp only [qf, dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    rw [Complex.star_def, Complex.conj_conj]; ring
  rw [e] at h
  exact (Complex.le_def.mp h).1

theorem isCompact_bdd (n : ℕ) (C : ℝ) :
    IsCompact {H : Matrix (Fin n) (Fin n) ℂ | ∀ j l, ‖H j l‖ ≤ C} := by
  have h : IsCompact (Set.pi Set.univ fun _ : Fin n => Set.pi Set.univ fun _ : Fin n =>
      closedBall (0 : ℂ) C) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 C
  have e : {H : Matrix (Fin n) (Fin n) ℂ | ∀ j l, ‖H j l‖ ≤ C} =
      (Set.pi Set.univ fun _ : Fin n => Set.pi Set.univ fun _ : Fin n =>
      closedBall (0 : ℂ) C : Set (Matrix (Fin n) (Fin n) ℂ)) := by
    ext H
    show _ ↔ ∀ j ∈ Set.univ, ∀ l ∈ Set.univ, H j l ∈ closedBall (0 : ℂ) C
    simp [mem_closedBall, dist_zero_right]
  rw [e]; exact h

theorem exists_det_bound (n : ℕ) (C : ℝ) : ∃ K : ℝ, 0 ≤ K ∧
    ∀ H : Matrix (Fin n) (Fin n) ℂ, (∀ j l, ‖H j l‖ ≤ C) → ‖H.det‖ ≤ K := by
  obtain ⟨K, hK⟩ := (isCompact_bdd n C).exists_bound_of_continuousOn
    (continuous_id.matrix_det).continuousOn
  refine ⟨max K 0, le_max_right _ _, fun H hH => (hK H hH).trans (le_max_left _ _)⟩

theorem exists_det_shift (n : ℕ) (C r : ℝ) (hr : 0 < r) : ∃ η : ℝ, 0 < η ∧
    ∀ H : Matrix (Fin n) (Fin n) ℂ, (∀ j l, ‖H j l‖ ≤ C) →
      ‖(H + (η : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).det - H.det‖ < r := by
  have hev : ∀ᶠ t : ℝ in 𝓝 0, ∀ H ∈ {H : Matrix (Fin n) (Fin n) ℂ | ∀ j l, ‖H j l‖ ≤ C},
      ‖(H + (t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).det - H.det‖ < r := by
    refine (isCompact_bdd n C).eventually_forall_of_forall_eventually fun H _ => ?_
    have hc : Continuous fun z : ℝ × Matrix (Fin n) (Fin n) ℂ =>
        ‖(z.2 + (z.1 : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).det - z.2.det‖ := by
      fun_prop
    have h0 : ‖(H + ((0 : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).det - H.det‖ = 0 := by simp
    have := hc.continuousAt (x := ((0 : ℝ), H))
    exact this.eventually (gt_mem_nhds (by simpa [h0] using hr))
  obtain ⟨t, ht, htpos⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin (s := Set.Ioi (0 : ℝ)) (a := 0))).exists
  exact ⟨t, htpos, fun H hH => ht H hH⟩

theorem qf_smul_one_re {n : ℕ} (c : ℝ) (w : V n) :
    (qf ((c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) w).re = c * ‖w‖ ^ 2 := by
  rw [qf_smul, qf_one, ← Complex.ofReal_mul, Complex.ofReal_re]

theorem qf_shift_re {n : ℕ} (m η : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) (w : V n) :
    (qf ((m : ℂ) • (H + (η : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))) w).re =
      m * ((qf H w).re + η * ‖w‖ ^ 2) := by
  rw [qf_smul, qf_add, qf_smul, qf_one, Complex.re_ofReal_mul, Complex.add_re,
    ← Complex.ofReal_mul, Complex.ofReal_re]

theorem trunc_lower {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosSemidef) (η δ : ℝ)
    (hη : 0 < η) (hδ : 0 < δ) (m : ℕ) (hm : 1 ≤ m) :
    Real.pi ^ n / (H + (η : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).det.re
        - Real.exp (-(m * η * δ ^ 2 / 2)) * (2 * Real.pi / η) ^ n ≤
      (m : ℝ) ^ n * ∫ w in ball (0 : V n) δ,
        Real.exp (-(m * ((qf H w).re + η * ‖w‖ ^ 2))) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  set Hη := H + (η : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) with hHη
  have hηpd : ((η : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosDef :=
    Matrix.PosDef.one.smul (a := η) hη
  have hHηpd : Hη.PosDef := Matrix.PosDef.posSemidef_add hH hηpd
  have hMpd : ((m : ℂ) • Hη).PosDef := hHηpd.smul (a := (m : ℝ)) hm0
  set b : ℝ := m * η / 2 with hb
  have hb0 : 0 < b := by positivity
  have hGpd : ((b : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosDef := Matrix.PosDef.one.smul (a := b) hb0
  obtain ⟨hfi, hfint⟩ := GlobalTheory.T.integral_exp_neg_hermitian_form_posDef n _ hMpd
  obtain ⟨hgi, hgint⟩ := GlobalTheory.T.integral_exp_neg_hermitian_form_posDef n _ hGpd
  set f : V n → ℝ := fun w => Real.exp (-(m * ((qf H w).re + η * ‖w‖ ^ 2))) with hf
  set g : V n → ℝ := fun w => Real.exp (-(b * ‖w‖ ^ 2)) with hg
  have ef : (fun w : V n => Real.exp (-(∑ j, ∑ l, ((m : ℂ) • Hη) j l * w j *
      (starRingEnd ℂ) (w l)).re)) = f := by
    funext w; exact congrArg (fun x => Real.exp (-x)) (qf_shift_re m η H w)
  have eg : (fun w : V n => Real.exp (-(∑ j, ∑ l, ((b : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) j l *
      w j * (starRingEnd ℂ) (w l)).re)) = g := by
    funext w; exact congrArg (fun x => Real.exp (-x)) (qf_smul_one_re b w)
  rw [ef] at hfi hfint
  rw [eg] at hgi hgint
  have hD : ((m : ℂ) • Hη).det.re = (m : ℝ) ^ n * Hη.det.re := by
    rw [Matrix.det_smul, Fintype.card_fin, show ((m : ℂ)) ^ n = (((m : ℝ) ^ n : ℝ) : ℂ) by push_cast; rfl,
      Complex.re_ofReal_mul]
  have hGd : ((b : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).det.re = b ^ n := by
    rw [Matrix.det_smul, Fintype.card_fin, Matrix.det_one, mul_one, ← Complex.ofReal_pow,
      Complex.ofReal_re]
  rw [hD] at hfint
  rw [hGd] at hgint
  have hDpos : 0 < Hη.det.re := by
    have := hHηpd.det_pos
    exact (Complex.lt_def.mp this).1

  have hsplit := integral_add_compl (s := ball (0 : V n) δ) measurableSet_ball hfi
  have htail : ∫ w in (ball (0 : V n) δ)ᶜ, f w ≤ Real.exp (-(m * η * δ ^ 2 / 2)) * ∫ w, g w := by
    rw [← integral_const_mul]
    refine (setIntegral_mono_on hfi.integrableOn (hgi.const_mul _).integrableOn
      measurableSet_ball.compl fun w hw => ?_).trans
      (setIntegral_le_integral (hgi.const_mul _) (Eventually.of_forall fun w => by positivity))
    have hw' : δ ≤ ‖w‖ := by simpa [mem_ball, dist_zero_right] using hw
    have hq := qf_re_nonneg H hH w
    simp only [hf, hg]
    rw [← Real.exp_add, Real.exp_le_exp]
    have h1 : δ ^ 2 ≤ ‖w‖ ^ 2 := pow_le_pow_left₀ hδ.le hw' 2
    have h2 : 0 ≤ (m : ℝ) * η := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h1 h2, mul_nonneg hm0.le hq]
  have hmain : (m : ℝ) ^ n * ∫ w in ball (0 : V n) δ, f w =
      Real.pi ^ n / Hη.det.re - (m : ℝ) ^ n * ∫ w in (ball (0 : V n) δ)ᶜ, f w := by
    rw [eq_sub_iff_add_eq, ← mul_add, hsplit, hfint]
    field_simp
  have hT : (m : ℝ) ^ n * (Real.exp (-(m * η * δ ^ 2 / 2)) * ∫ w, g w) =
      Real.exp (-(m * η * δ ^ 2 / 2)) * (2 * Real.pi / η) ^ n := by
    rw [hgint, hb]
    field_simp
    have h1 : η ^ n * η⁻¹ ^ n = 1 := by rw [← mul_pow, mul_inv_cancel₀ hη.ne', one_pow]
    have h2 : (1 / 2 : ℝ) ^ n * 2 ^ n = 1 := by rw [← mul_pow]; norm_num
    linear_combination (-((m : ℝ) ^ n * Real.pi ^ n * (1 / 2 : ℝ) ^ n * 2 ^ n)) * h1 -
      ((m : ℝ) ^ n * Real.pi ^ n) * h2
  show _ ≤ (m : ℝ) ^ n * ∫ w in ball (0 : V n) δ, f w
  rw [hmain, ← hT]
  have := mul_le_mul_of_nonneg_left htail (pow_nonneg hm0.le n)
  linarith

theorem trunc_gauss : ∀ (n : ℕ) (C ε : ℝ), 0 < ε → ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ →
    ∀ᶠ m : ℕ in atTop, ∀ H : Matrix (Fin n) (Fin n) ℂ, H.PosSemidef → (∀ j l, ‖H j l‖ ≤ C) →
      1 ≤ (H.det.re / Real.pi ^ n + ε) * (m : ℝ) ^ n * ∫ w in ball (0 : V n) δ,
        Real.exp (-(m * ((∑ j, ∑ l, H j l * w j * (starRingEnd ℂ) (w l)).re + η * ‖w‖ ^ 2))) := by
  intro n C ε hε
  set P : ℝ := Real.pi ^ n with hPdef
  have hP : 0 < P := pow_pos Real.pi_pos n
  set r : ℝ := ε * P / 2 with hrdef
  have hr : 0 < r := by positivity
  obtain ⟨K, hK0, hK⟩ := exists_det_bound n C
  obtain ⟨η, hη, hηd⟩ := exists_det_shift n C r hr
  refine ⟨η, hη, fun δ hδ => ?_⟩
  set A : ℝ := K / P + ε with hAdef
  have hA : 0 < A := by positivity
  set K2 : ℝ := K + r with hK2def
  have hK2 : 0 < K2 := by positivity
  have hs : 0 < r / K2 / A := by positivity
  have hT : Tendsto (fun m : ℕ => Real.exp (-(m * η * δ ^ 2 / 2)) * (2 * Real.pi / η) ^ n)
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun m : ℕ => (m : ℝ) * (η * δ ^ 2 / 2)) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_mul_const (by positivity)
    have h2 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).mul_const ((2 * Real.pi / η) ^ n)
    rw [zero_mul] at h2
    refine h2.congr fun m => ?_
    simp only [Function.comp_apply]
    congr 2
    ring
  filter_upwards [hT.eventually (gt_mem_nhds hs), eventually_ge_atTop 1] with m hm hm1
  intro H hH hC
  have hl := trunc_lower H hH η δ hη hδ m hm1
  show 1 ≤ _ * _ * ∫ w in ball (0 : V n) δ, Real.exp (-(m * ((qf H w).re + η * ‖w‖ ^ 2)))
  set I := ∫ w in ball (0 : V n) δ, Real.exp (-(m * ((qf H w).re + η * ‖w‖ ^ 2)))
  set T := Real.exp (-(m * η * δ ^ 2 / 2)) * (2 * Real.pi / η) ^ n with hTdef
  have hT0 : 0 ≤ T := by positivity
  set d := H.det.re with hddef
  set D := (H + (η : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).det.re with hDdef
  have hd0 : 0 ≤ d := by
    have := (Complex.le_def.mp hH.det_nonneg).1
    simpa using this
  have hdK : d ≤ K := (Complex.re_le_norm _).trans (hK H hC)
  have hDd : D - d < r := by
    have := (Complex.re_le_norm _).trans_lt (hηd H hC)
    rw [Complex.sub_re] at this; exact this
  have hDpos : 0 < D := by
    have hηpd : ((η : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosDef :=
      Matrix.PosDef.one.smul (a := η) hη
    exact (Complex.lt_def.mp (Matrix.PosDef.posSemidef_add hH hηpd).det_pos).1
  have e1 : (d / P + ε) * (P / D) = (d + ε * P) / D := by field_simp
  have e2 : r / K2 ≤ r / D := div_le_div_of_nonneg_left hr.le hDpos (by linarith)
  have e3 : 1 + r / D ≤ (d + ε * P) / D := by
    rw [le_div_iff₀ hDpos, add_mul, div_mul_cancel₀ _ hDpos.ne']
    linarith
  have e4 : (d / P + ε) * T ≤ A * T :=
    mul_le_mul_of_nonneg_right (by have := div_le_div_of_nonneg_right hdK hP.le; linarith) hT0
  have e5 : A * T < r / K2 := by
    have := (lt_div_iff₀ hA).mp hm
    linarith
  have e6 : (d / P + ε) * (P / D - T) ≤ (d / P + ε) * ((m : ℝ) ^ n * I) :=
    mul_le_mul_of_nonneg_left hl (by positivity)
  rw [mul_assoc]
  rw [mul_sub, e1] at e6
  linarith

end GlobalTheory.TruncGauss
