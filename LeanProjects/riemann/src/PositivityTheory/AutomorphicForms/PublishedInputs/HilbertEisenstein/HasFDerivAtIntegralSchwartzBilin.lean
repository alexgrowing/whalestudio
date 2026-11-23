import Mathlib

open MeasureTheory Filter Topology
open scoped SchwartzMap ContDiff

noncomputable section

namespace UpperTheory.HilbertEisensteinWeightOne.EisensteinSmoothness

set_option linter.unusedSectionVars false

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]

theorem natCast_le_infty (m : ℕ) : (m : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.2 le_top

theorem natCast_lt_infty (m : ℕ) : (m : WithTop ℕ∞) < ∞ := WithTop.coe_lt_coe.2 (ENat.natCast_lt_top m)

theorem infty_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by simp

def bilD (Ψ : 𝓢(V, ℂ)) (B : V →L[ℝ] X →L[ℝ] V) (m : ℕ) (v : V) (x : X) :
    ContinuousMultilinearMap ℝ (fun _ : Fin m => X) ℂ :=
  iteratedFDeriv ℝ m (fun x => Ψ (B v x)) x

theorem contDiff_bil (Ψ : 𝓢(V, ℂ)) (B : V →L[ℝ] X →L[ℝ] V) (v : V) :
    ContDiff ℝ ∞ (fun x => Ψ (B v x)) :=
  (Ψ.smooth ⊤).comp (B v).contDiff

theorem bilD_eq (Ψ : 𝓢(V, ℂ)) (B : V →L[ℝ] X →L[ℝ] V) (m : ℕ) (v : V) (x : X) :
    bilD Ψ B m v x = (iteratedFDeriv ℝ m Ψ (B v x)).compContinuousLinearMap fun _ => B v :=
  (B v).iteratedFDeriv_comp_right (Ψ.smooth ⊤) x (natCast_le_infty m)

theorem continuous_compCLM (m : ℕ) :
    Continuous (fun fg : ContinuousMultilinearMap ℝ (fun _ : Fin m => V) ℂ × (Fin m → X →L[ℝ] V) =>
      fg.1.compContinuousLinearMap fg.2) :=
  continuous_iff_continuousAt.2 fun fg =>
    (ContinuousMultilinearMap.hasStrictFDerivAt_compContinuousLinearMap fg).hasFDerivAt.continuousAt

theorem continuous_bilD_left (Ψ : 𝓢(V, ℂ)) (B : V →L[ℝ] X →L[ℝ] V) (m : ℕ) (x : X) :
    Continuous fun v => bilD Ψ B m v x := by
  have h1 : Continuous fun v => B v x := B.continuous.clm_apply continuous_const
  have h2 : Continuous fun v => iteratedFDeriv ℝ m Ψ (B v x) :=
    ((Ψ.smooth ⊤).continuous_iteratedFDeriv (natCast_le_infty m)).comp h1
  have h3 : Continuous fun v => (fun _ : Fin m => B v) := continuous_pi fun _ => B.continuous
  have h := (continuous_compCLM (V := V) (X := X) m).comp (h2.prodMk h3)
  refine h.congr fun v => ?_
  exact (bilD_eq Ψ B m v x).symm

theorem continuous_fderiv_bil_left (Ψ : 𝓢(V, ℂ)) (B : V →L[ℝ] X →L[ℝ] V) (x : X) :
    Continuous fun v => fderiv ℝ (fun x => Ψ (B v x)) x := by
  have h1 : Continuous fun v => B v x := B.continuous.clm_apply continuous_const
  have h2 : Continuous fun v => fderiv ℝ Ψ (B v x) :=
    ((Ψ.smooth ⊤).continuous_fderiv infty_ne_zero).comp h1
  have h := h2.clm_comp B.continuous
  refine h.congr fun v => ?_
  have hd : HasFDerivAt (fun x => Ψ (B v x)) ((fderiv ℝ Ψ (B v x)).comp (B v)) x :=
    (((Ψ.smooth ⊤).differentiable infty_ne_zero) (B v x)).hasFDerivAt.comp x (B v).hasFDerivAt
  exact hd.fderiv.symm

theorem exists_bound_bilD (Ψ : 𝓢(V, ℂ)) (B : V →L[ℝ] X →L[ℝ] V) {U : Set X} {c : ℝ} (hc : 0 < c)
    (hB : ∀ x ∈ U, ∀ v, c * ‖v‖ ≤ ‖B v x‖) (m k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ U, ∀ v, ‖bilD Ψ B m v x‖ ≤ C * ((1 + ‖v‖) ^ k)⁻¹ := by
  set S : ℝ := 2 ^ (k + m) *
    (Finset.Iic (k + m, m)).sup (fun p : ℕ × ℕ => SchwartzMap.seminorm ℝ p.1 p.2) Ψ with hSdef
  have hS : 0 ≤ S := mul_nonneg (by positivity) (apply_nonneg _ _)
  set c' := min 1 c
  have hc' : 0 < c' := lt_min one_pos hc
  refine ⟨S * ‖B‖ ^ m / c' ^ (k + m), by positivity, fun x hx v => ?_⟩
  have hp : 0 < 1 + ‖v‖ := by positivity
  have hq : c' * (1 + ‖v‖) ≤ 1 + ‖B v x‖ := by
    have h0 := hB x hx v
    have h1 : c' ≤ 1 := min_le_left _ _
    have h2 : c' ≤ c := min_le_right _ _
    nlinarith [norm_nonneg v]
  have hSch : (1 + ‖B v x‖) ^ (k + m) * ‖iteratedFDeriv ℝ m Ψ (B v x)‖ ≤ S :=
    SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k + m, m)) le_rfl le_rfl Ψ (B v x)
  have hBv : ‖B v‖ ≤ ‖B‖ * (1 + ‖v‖) :=
    (B.le_opNorm v).trans (mul_le_mul_of_nonneg_left (by linarith [norm_nonneg v]) (norm_nonneg _))
  have hcomp : ‖bilD Ψ B m v x‖ ≤ ‖iteratedFDeriv ℝ m Ψ (B v x)‖ * ‖B v‖ ^ m := by
    rw [bilD_eq]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    simp [Finset.prod_const]
  have hI : ‖iteratedFDeriv ℝ m Ψ (B v x)‖ ≤ S / (c' * (1 + ‖v‖)) ^ (k + m) := by
    rw [le_div_iff₀ (by positivity)]
    calc ‖iteratedFDeriv ℝ m Ψ (B v x)‖ * (c' * (1 + ‖v‖)) ^ (k + m)
        ≤ ‖iteratedFDeriv ℝ m Ψ (B v x)‖ * (1 + ‖B v x‖) ^ (k + m) := by gcongr
      _ ≤ S := by linarith [hSch]
  have hp' := hp.ne'
  have hc'' := hc'.ne'
  calc ‖bilD Ψ B m v x‖ ≤ ‖iteratedFDeriv ℝ m Ψ (B v x)‖ * ‖B v‖ ^ m := hcomp
    _ ≤ S / (c' * (1 + ‖v‖)) ^ (k + m) * (‖B‖ * (1 + ‖v‖)) ^ m := by gcongr
    _ = S * ‖B‖ ^ m / c' ^ (k + m) * ((1 + ‖v‖) ^ k)⁻¹ := by
        rw [mul_pow, mul_pow, pow_add, pow_add]
        field_simp

section Main

variable (Ψ : 𝓢(V, ℂ)) (B : V →L[ℝ] X →L[ℝ] V) {U : Set X} (hU : IsOpen U) {c : ℝ} (hc : 0 < c)
    (hB : ∀ x ∈ U, ∀ v, c * ‖v‖ ≤ ‖B v x‖)
    {κ : α → ℂ} {w : α → V} (hκ : AEStronglyMeasurable κ μ) (hw : AEStronglyMeasurable w μ)
    {k : ℕ} (hint : Integrable (fun a => ‖κ a‖ * ((1 + ‖w a‖) ^ k)⁻¹) μ)

include hc hB hκ hw hint in
theorem integrable_schwartz_bilin {x : X} (hx : x ∈ U) :
    Integrable (fun a => κ a * Ψ (B (w a) x)) μ := by
  obtain ⟨C, -, hC⟩ := exists_bound_bilD Ψ B hc hB 0 k
  have hm : AEStronglyMeasurable (fun a => κ a * Ψ (B (w a) x)) μ :=
    hκ.mul ((Ψ.continuous.comp (B.continuous.clm_apply continuous_const)).comp_aestronglyMeasurable hw)
  refine (hint.const_mul C).mono' hm (ae_of_all _ fun a => ?_)
  have h := hC x hx (w a)
  rw [bilD, norm_iteratedFDeriv_zero] at h
  rw [norm_mul]
  calc ‖κ a‖ * ‖Ψ (B (w a) x)‖ ≤ ‖κ a‖ * (C * ((1 + ‖w a‖) ^ k)⁻¹) :=
        mul_le_mul_of_nonneg_left h (norm_nonneg _)
    _ = C * (‖κ a‖ * ((1 + ‖w a‖) ^ k)⁻¹) := by ring

include hU hc hB hκ hw hint in
theorem hasFDerivAt_integral_schwartz_bilin {x : X} (hx : x ∈ U) :
    HasFDerivAt (fun x => ∫ a, κ a * Ψ (B (w a) x) ∂μ)
      (∫ a, κ a • fderiv ℝ (fun x => Ψ (B (w a) x)) x ∂μ) x := by
  obtain ⟨C, -, hC⟩ := exists_bound_bilD Ψ B hc hB 1 k
  have hbd : ∀ y ∈ U, ∀ a, ‖κ a • fderiv ℝ (fun x => Ψ (B (w a) x)) y‖ ≤
      C * (‖κ a‖ * ((1 + ‖w a‖) ^ k)⁻¹) := by
    intro y hy a
    have h := hC y hy (w a)
    rw [bilD, ← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_zero] at h
    rw [norm_smul]
    calc ‖κ a‖ * ‖fderiv ℝ (fun x => Ψ (B (w a) x)) y‖ ≤ ‖κ a‖ * (C * ((1 + ‖w a‖) ^ k)⁻¹) :=
          mul_le_mul_of_nonneg_left h (norm_nonneg _)
      _ = C * (‖κ a‖ * ((1 + ‖w a‖) ^ k)⁻¹) := by ring
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun x a => κ a * Ψ (B (w a) x))
    (F' := fun x a => κ a • fderiv ℝ (fun x => Ψ (B (w a) x)) x) (hU.mem_nhds hx) ?_
    (integrable_schwartz_bilin Ψ B hc hB hκ hw hint hx) ?_ ?_ (hint.const_mul C) ?_
  · exact Filter.Eventually.of_forall fun y =>
      hκ.mul ((Ψ.continuous.comp (B.continuous.clm_apply continuous_const)).comp_aestronglyMeasurable hw)
  · exact hκ.smul ((continuous_fderiv_bil_left Ψ B x).comp_aestronglyMeasurable hw)
  · exact ae_of_all _ fun a y hy => hbd y hy a
  · refine ae_of_all _ fun a y _ => ?_
    exact (((contDiff_bil Ψ B (w a)).differentiable infty_ne_zero) y).hasFDerivAt.const_mul (κ a)

include hU hc hB hκ hw hint in
theorem contDiffOn_integral_schwartz_bilin :
    ContDiffOn ℝ ∞ (fun x => ∫ a, κ a * Ψ (B (w a) x) ∂μ) U := by
  classical
  choose C hC0 hC using fun m => exists_bound_bilD Ψ B hc hB m k
  have hmeas : ∀ m x, AEStronglyMeasurable (fun a => κ a • bilD Ψ B m (w a) x) μ := fun m x =>
    hκ.smul ((continuous_bilD_left Ψ B m x).comp_aestronglyMeasurable hw)
  have hbd : ∀ m, ∀ x ∈ U, ∀ a, ‖κ a • bilD Ψ B m (w a) x‖ ≤
      C m * (‖κ a‖ * ((1 + ‖w a‖) ^ k)⁻¹) := by
    intro m x hx a
    rw [norm_smul]
    calc ‖κ a‖ * ‖bilD Ψ B m (w a) x‖ ≤ ‖κ a‖ * (C m * ((1 + ‖w a‖) ^ k)⁻¹) :=
          mul_le_mul_of_nonneg_left (hC m x hx (w a)) (norm_nonneg _)
      _ = C m * (‖κ a‖ * ((1 + ‖w a‖) ^ k)⁻¹) := by ring
  have hint' : ∀ m, ∀ x ∈ U, Integrable (fun a => κ a • bilD Ψ B m (w a) x) μ := fun m x hx =>
    (hint.const_mul (C m)).mono' (hmeas m x) (ae_of_all _ (hbd m x hx))
  let p : X → FormalMultilinearSeries ℝ X ℂ := fun x m => ∫ a, κ a • bilD Ψ B m (w a) x ∂μ
  have hTay : HasFTaylorSeriesUpToOn ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x => ∫ a, κ a * Ψ (B (w a) x) ∂μ) p U := by
    refine ⟨fun x hx => ?_, fun m _ x hx => ?_, fun m _ => ?_⟩
    · show (∫ a, κ a • bilD Ψ B 0 (w a) x ∂μ) 0 = _
      rw [ContinuousMultilinearMap.integral_apply (hint' 0 x hx)]
      simp [bilD]
    · let L := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => X) ℂ
      have hL : (p x m.succ).curryLeft = ∫ a, L (κ a • bilD Ψ B (m + 1) (w a) x) ∂μ :=
        (L.toContinuousLinearEquiv.integral_comp_comm (μ := μ)
          (fun a => κ a • bilD Ψ B (m + 1) (w a) x)).symm
      rw [hL]
      show HasFDerivWithinAt (fun y => ∫ a, κ a • bilD Ψ B m (w a) y ∂μ) _ U x
      refine (hasFDerivAt_integral_of_dominated_of_fderiv_le
        (F := fun y a => κ a • bilD Ψ B m (w a) y)
        (F' := fun y a => L (κ a • bilD Ψ B (m + 1) (w a) y)) (hU.mem_nhds hx)
        (Filter.Eventually.of_forall fun y => hmeas m y) (hint' m x hx)
        (L.continuous.comp_aestronglyMeasurable (hmeas (m + 1) x)) ?_
        (hint.const_mul (C (m + 1))) ?_).hasFDerivWithinAt
      · exact ae_of_all _ fun a y hy => by rw [L.norm_map]; exact hbd (m + 1) y hy a
      · refine ae_of_all _ fun a y _ => ?_
        have h := ((contDiff_bil Ψ B (w a)).ftaylorSeries).fderiv m (natCast_lt_infty m) y
        have h2 := h.const_smul (κ a)
        have e : L (κ a • bilD Ψ B (m + 1) (w a) y) =
            κ a • (ftaylorSeries ℝ (fun x => Ψ (B (w a) x)) y m.succ).curryLeft := by
          ext v u
          simp [L, bilD, ftaylorSeries]
        rw [e]
        exact h2
    · exact continuousOn_of_dominated (fun x _ => hmeas m x) (fun x hx => ae_of_all _ (hbd m x hx))
        (hint.const_mul (C m)) (ae_of_all _ fun a => by
          have hc1 : Continuous fun y => bilD Ψ B m (w a) y :=
            (contDiff_bil Ψ B (w a)).continuous_iteratedFDeriv (natCast_le_infty m)
          exact (hc1.const_smul (κ a)).continuousOn)
  exact hTay.contDiffOn

end Main

end UpperTheory.HilbertEisensteinWeightOne.EisensteinSmoothness
