import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocallyConstantMajorants.GammaSplitting.ComplexMatrixMajorantIntegrable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableMulCIff

noncomputable section

open MeasureTheory Matrix
open Ad3.K Ad3.K.LC Ad3.K.LC.C GlobalTheory.CompanionTheory.GodementFE

namespace GlobalTheory.CompanionTheory.GodementFE.Unif

abbrev Sp := SchwartzMap (Fin 2 → ℂ) ℂ

def P6 : Seminorm ℝ Sp :=
  (Finset.Iic ((6, 0) : ℕ × ℕ)).sup (schwartzSeminormFamily ℝ (Fin 2 → ℂ) ℂ)

theorem seminorm_le_pS {N i j : ℕ} (hi : i ≤ N) (hj : j ≤ N) (f : Sp) :
    SchwartzMap.seminorm ℝ i j f ≤ pS N f := by
  unfold pS
  calc SchwartzMap.seminorm ℝ i j f
      ≤ ∑ j ∈ Finset.range (N + 1), SchwartzMap.seminorm ℝ i j f :=
        Finset.single_le_sum (f := fun j => SchwartzMap.seminorm ℝ i j f)
          (fun _ _ => apply_nonneg _ _) (Finset.mem_range.2 (by omega))
    _ ≤ _ :=
        Finset.single_le_sum
          (f := fun i => ∑ j ∈ Finset.range (N + 1), SchwartzMap.seminorm ℝ i j f)
          (fun _ _ => Finset.sum_nonneg fun _ _ => apply_nonneg _ _)
          (Finset.mem_range.2 (by omega))

theorem pS_nonneg (N : ℕ) (f : Sp) : 0 ≤ pS N f :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => apply_nonneg _ _

theorem pS_mono {N M : ℕ} (h : N ≤ M) (f : Sp) : pS N f ≤ pS M f := by
  unfold pS
  refine (Finset.sum_le_sum fun i _ => Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (by omega)) (fun _ _ _ => apply_nonneg _ _)).trans
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      (fun _ _ _ => Finset.sum_nonneg fun _ _ => apply_nonneg _ _))

theorem sup_le_pS (s : Finset (ℕ × ℕ)) {N : ℕ} (h : ∀ i ∈ s, i.1 ≤ N ∧ i.2 ≤ N) (f : Sp) :
    (s.sup (schwartzSeminormFamily ℝ (Fin 2 → ℂ) ℂ)) f ≤ pS N f :=
  Seminorm.finset_sup_apply_le (pS_nonneg N f) fun i hi =>
    seminorm_le_pS (h i hi).1 (h i hi).2 f

theorem P6_le_pS_six (f : Sp) : P6 f ≤ pS 6 f := by
  refine sup_le_pS _ (fun i hi => ?_) f
  have h := Finset.mem_Iic.1 hi
  have h1 : i.1 ≤ 6 := h.1
  have h2 : i.2 ≤ 0 := h.2
  exact ⟨h1, by omega⟩

theorem continuous_P6 : Continuous P6 :=
  Seminorm.continuous_finsetSup fun i _ =>
    (schwartz_withSeminorms ℝ (Fin 2 → ℂ) ℂ).continuous_seminorm i

theorem exists_P6_comp_le_mul_seminorm (T : Sp →L[ℝ] Sp) :
    ∃ (N : ℕ) (D : ℝ), 0 ≤ D ∧ ∀ f : Sp, P6 (T f) ≤ D * pS N f := by
  let q : Seminorm ℝ Sp := P6.comp T.toLinearMap
  have hq : Continuous q := continuous_P6.comp T.continuous
  obtain ⟨u, C, -, hle⟩ :=
    Seminorm.bound_of_continuous (schwartz_withSeminorms ℝ (Fin 2 → ℂ) ℂ) q hq
  refine ⟨u.sup fun i => max i.1 i.2, C, C.2, fun f => ?_⟩
  have h1 : q f ≤ (C : ℝ) * (u.sup (schwartzSeminormFamily ℝ (Fin 2 → ℂ) ℂ)) f := hle f
  refine h1.trans (mul_le_mul_of_nonneg_left (sup_le_pS u (fun i hi => ?_) f) C.2)
  have := Finset.le_sup (f := fun i : ℕ × ℕ => max i.1 i.2) hi
  exact ⟨(le_max_left _ _).trans this, (le_max_right _ _).trans this⟩

theorem schw_unif (f : Sp) (x u : ℂ) : ‖f ![x, u]‖ ≤ 2 ^ 6 * P6 f * (dd x * dd u ^ 2) := by
  set K : ℝ := 2 ^ 6 * P6 f with hK
  set v : Fin 2 → ℂ := ![x, u] with hv
  have h : (1 + ‖v‖) ^ 6 * ‖f v‖ ≤ K := by
    have := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (6, 0)) (k := 6) (n := 0)
      le_rfl le_rfl f v
    rw [norm_iteratedFDeriv_zero] at this
    exact this
  have hx : ‖x‖ ≤ ‖v‖ := by simpa [hv] using norm_le_pi_norm v 0
  have hu : ‖u‖ ≤ ‖v‖ := by simpa [hv] using norm_le_pi_norm v 1
  have hr : 0 ≤ ‖v‖ := norm_nonneg _
  have hA : 1 + ‖x‖ ^ 2 ≤ (1 + ‖v‖) ^ 2 := by nlinarith [norm_nonneg x]
  have hB : 1 + ‖u‖ ^ 2 ≤ (1 + ‖v‖) ^ 2 := by nlinarith [norm_nonneg u]
  have hAB : (1 + ‖x‖ ^ 2) * (1 + ‖u‖ ^ 2) ^ 2 ≤ (1 + ‖v‖) ^ 6 := by
    have h2 : (1 + ‖u‖ ^ 2) ^ 2 ≤ ((1 + ‖v‖) ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) hB 2
    calc (1 + ‖x‖ ^ 2) * (1 + ‖u‖ ^ 2) ^ 2 ≤ (1 + ‖v‖) ^ 2 * ((1 + ‖v‖) ^ 2) ^ 2 :=
          mul_le_mul hA h2 (by positivity) (by positivity)
      _ = (1 + ‖v‖) ^ 6 := by ring
  have h3 : (1 + ‖x‖ ^ 2) * (1 + ‖u‖ ^ 2) ^ 2 * ‖f v‖ ≤ K :=
    le_trans (mul_le_mul_of_nonneg_right hAB (norm_nonneg _)) h
  have hpos : 0 < (1 + ‖x‖ ^ 2) * (1 + ‖u‖ ^ 2) ^ 2 := by positivity
  have e : K * (dd x * dd u ^ 2) = K / ((1 + ‖x‖ ^ 2) * (1 + ‖u‖ ^ 2) ^ 2) := by
    simp only [dd]
    field_simp
  rw [e, le_div_iff₀ hpos, mul_comm]
  exact h3

def c0 : ℝ := 2 ^ 6 * ∫ u : ℂ, dd u ^ 2

theorem weightConst_nonneg : 0 ≤ c0 := by
  have hJ : 0 ≤ ∫ u : ℂ, dd u ^ 2 := integral_nonneg fun u => by positivity
  unfold c0
  positivity

theorem sF_bound_unif (f : Sp) (x ξ : ℂ) : ‖sF f x ξ‖ ≤ c0 * P6 f * dd x := by
  have h1 : ‖sF f x ξ‖ ≤ ∫ u : ℂ, 2 ^ 6 * P6 f * dd x * dd u ^ 2 := by
    refine norm_integral_le_of_norm_le (dd_sq_int.const_mul _)
      (Filter.Eventually.of_forall fun u => ?_)
    rw [norm_mul, norm_psiC, mul_one]
    calc ‖f ![x, u]‖ ≤ 2 ^ 6 * P6 f * (dd x * dd u ^ 2) := schw_unif f x u
      _ = _ := by ring
  rw [integral_const_mul] at h1
  calc _ ≤ _ := h1
    _ = _ := by unfold c0; ring

theorem decay_of_bounds (f : Sp) (C0 C1 C2 : ℝ) (x ξ : ℂ)
    (b0 : ‖sF f x ξ‖ ≤ C0 * dd x)
    (b1 : ‖sF (LineDeriv.lineDerivOp (![0, 1] : Fin 2 → ℂ)
      (LineDeriv.lineDerivOp (![0, 1] : Fin 2 → ℂ) f)) x ξ‖ ≤ C1 * dd x)
    (b2 : ‖sF (LineDeriv.lineDerivOp (![0, Complex.I] : Fin 2 → ℂ)
      (LineDeriv.lineDerivOp (![0, Complex.I] : Fin 2 → ℂ) f)) x ξ‖ ≤ C2 * dd x) :
    ‖sF f x ξ‖ ≤ (C0 + C1 + C2) * (dd x * dd ξ) := by
  have e1 : sF (LineDeriv.lineDerivOp (![0, 1] : Fin 2 → ℂ)
      (LineDeriv.lineDerivOp (![0, 1] : Fin 2 → ℂ) f)) x ξ =
      (-(4 * Real.pi * Complex.I * ξ.re)) ^ 2 * sF f x ξ := by
    rw [sF_deriv, sF_deriv]
    simp only [one_mul]
    ring
  have e2 : sF (LineDeriv.lineDerivOp (![0, Complex.I] : Fin 2 → ℂ)
      (LineDeriv.lineDerivOp (![0, Complex.I] : Fin 2 → ℂ) f)) x ξ =
      (-(4 * Real.pi * Complex.I * ξ.im)) ^ 2 * sF f x ξ := by
    rw [sF_deriv, sF_deriv]
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub]
    push_cast
    ring
  have n1 : (4 * Real.pi) ^ 2 * ξ.re ^ 2 * ‖sF f x ξ‖ ≤ C1 * dd x := by
    have := b1
    rw [e1, norm_mul, norm_pow, norm_neg] at this
    have e : ‖4 * (Real.pi : ℂ) * Complex.I * (ξ.re : ℂ)‖ = 4 * Real.pi * |ξ.re| := by
      simp [abs_of_pos Real.pi_pos]
    rw [e, mul_pow, sq_abs] at this
    exact this
  have n2 : (4 * Real.pi) ^ 2 * ξ.im ^ 2 * ‖sF f x ξ‖ ≤ C2 * dd x := by
    have := b2
    rw [e2, norm_mul, norm_pow, norm_neg] at this
    have e : ‖4 * (Real.pi : ℂ) * Complex.I * (ξ.im : ℂ)‖ = 4 * Real.pi * |ξ.im| := by
      simp [abs_of_pos Real.pi_pos]
    rw [e, mul_pow, sq_abs] at this
    exact this
  have hpi : (1 : ℝ) ≤ (4 * Real.pi) ^ 2 := by nlinarith [Real.pi_gt_three]
  have hsq : ‖ξ‖ ^ 2 = ξ.re ^ 2 + ξ.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have hS : 0 ≤ ‖sF f x ξ‖ := norm_nonneg _
  have hmain : (1 + ‖ξ‖ ^ 2) * ‖sF f x ξ‖ ≤ (C0 + C1 + C2) * dd x := by
    rw [hsq]
    have a1 : ξ.re ^ 2 * ‖sF f x ξ‖ ≤ (4 * Real.pi) ^ 2 * ξ.re ^ 2 * ‖sF f x ξ‖ := by
      have : 0 ≤ ξ.re ^ 2 * ‖sF f x ξ‖ := by positivity
      nlinarith
    have a2 : ξ.im ^ 2 * ‖sF f x ξ‖ ≤ (4 * Real.pi) ^ 2 * ξ.im ^ 2 * ‖sF f x ξ‖ := by
      have : 0 ≤ ξ.im ^ 2 * ‖sF f x ξ‖ := by positivity
      nlinarith
    nlinarith
  have hpos : 0 < 1 + ‖ξ‖ ^ 2 := by positivity
  have e : (C0 + C1 + C2) * (dd x * dd ξ) = (C0 + C1 + C2) * dd x / (1 + ‖ξ‖ ^ 2) := by
    simp only [dd]
    field_simp
  rw [e, le_div_iff₀ hpos, mul_comm]
  exact hmain

def T2 (e : ℂ) : Sp →L[ℝ] Sp :=
  (LineDeriv.lineDerivOpCLM ℝ Sp (![0, e] : Fin 2 → ℂ)).comp
    (LineDeriv.lineDerivOpCLM ℝ Sp (![0, e] : Fin 2 → ℂ))

theorem secondLineDeriv_apply (e : ℂ) (f : Sp) :
    T2 e f = LineDeriv.lineDerivOp (![0, e] : Fin 2 → ℂ)
      (LineDeriv.lineDerivOp (![0, e] : Fin 2 → ℂ) f) := by
  simp [T2, LineDeriv.lineDerivOpCLM_apply]

theorem sF_decay_unif : ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ (f : SchwartzMap (Fin 2 → ℂ) ℂ) (x ξ : ℂ),
    ‖sF f x ξ‖ ≤ C * pS N f * (dd x * dd ξ) := by
  obtain ⟨N1, D1, hD1, b1⟩ := exists_P6_comp_le_mul_seminorm (T2 1)
  obtain ⟨N2, D2, hD2, b2⟩ := exists_P6_comp_le_mul_seminorm (T2 Complex.I)
  have hc := weightConst_nonneg
  refine ⟨c0 * (1 + D1 + D2), max 6 (max N1 N2), by positivity, fun f x ξ => ?_⟩
  set N := max 6 (max N1 N2) with hN
  set A := pS N f with hA
  have h0 : P6 f ≤ A := (P6_le_pS_six f).trans (pS_mono (le_max_left _ _) f)
  have h1 : P6 (T2 1 f) ≤ D1 * A :=
    (b1 f).trans (mul_le_mul_of_nonneg_left
      (pS_mono ((le_max_left _ _).trans (le_max_right _ _)) f) hD1)
  have h2 : P6 (T2 Complex.I f) ≤ D2 * A :=
    (b2 f).trans (mul_le_mul_of_nonneg_left
      (pS_mono ((le_max_right _ _).trans (le_max_right _ _)) f) hD2)
  have hdx := (dd_pos x).le
  have key : ∀ (g : Sp) (B : ℝ), P6 g ≤ B → ‖sF g x ξ‖ ≤ c0 * B * dd x := fun g B hB =>
    (sF_bound_unif g x ξ).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hB hc) hdx)
  have := decay_of_bounds f (c0 * A) (c0 * (D1 * A)) (c0 * (D2 * A)) x ξ (key f A h0)
    (by rw [← secondLineDeriv_apply]; exact key _ _ h1) (by rw [← secondLineDeriv_apply]; exact key _ _ h2)
  calc _ ≤ _ := this
    _ = _ := by ring

end GlobalTheory.CompanionTheory.GodementFE.Unif
