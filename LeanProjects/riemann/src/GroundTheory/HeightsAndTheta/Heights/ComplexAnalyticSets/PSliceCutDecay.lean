import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceCutDecay
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StMaDensChain
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceLevelSet
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceMassFinite
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceIdeal
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PMaDensLeibniz
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetSumMeasurable
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCutOffDominated
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCutOffGradient
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StokesOffDiscriminantWindow
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.LogIntegrableOnOfLogIntegrable
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open scoped ContDiff

noncomputable section

namespace SliceCutDecay

def prof (c u : ℝ) : ℝ := Real.smoothTransition (2 - u / c)

theorem contDiff_tau : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff

theorem contDiff_tau' : ContDiff ℝ ∞ (deriv Real.smoothTransition) :=
  (contDiff_infty_iff_deriv.mp contDiff_tau).2

theorem contDiff_tau'' : ContDiff ℝ ∞ (deriv (deriv Real.smoothTransition)) :=
  (contDiff_infty_iff_deriv.mp contDiff_tau').2

theorem tau_eventually_const {u : ℝ} (hu : u ∉ Set.Icc (0 : ℝ) 1) :
    ∃ a : ℝ, Real.smoothTransition =ᶠ[𝓝 u] fun _ => a := by
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hu
  rcases hu with hu | hu
  · exact ⟨0, Filter.eventually_of_mem (Iio_mem_nhds hu) fun v hv =>
      Real.smoothTransition.zero_of_nonpos (le_of_lt hv)⟩
  · exact ⟨1, Filter.eventually_of_mem (Ioi_mem_nhds hu) fun v hv =>
      Real.smoothTransition.one_of_one_le (le_of_lt hv)⟩

theorem tau'_eq_zero {u : ℝ} (hu : u ∉ Set.Icc (0 : ℝ) 1) : deriv Real.smoothTransition u = 0 := by
  obtain ⟨a, ha⟩ := tau_eventually_const hu
  rw [ha.deriv_eq]
  simp

theorem tau''_eq_zero {u : ℝ} (hu : u ∉ Set.Icc (0 : ℝ) 1) :
    deriv (deriv Real.smoothTransition) u = 0 := by
  have : deriv Real.smoothTransition =ᶠ[𝓝 u] fun _ => (0 : ℝ) := by
    filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds hu] with v hv using tau'_eq_zero hv
  rw [this.deriv_eq]
  simp

theorem hasDerivAt_inner (c u : ℝ) : HasDerivAt (fun u => 2 - u / c) (-(1 / c)) u := by
  simpa using ((hasDerivAt_id u).div_const c).const_sub 2

theorem contDiff_prof (c : ℝ) : ContDiff ℝ ∞ (prof c) :=
  contDiff_tau.comp (contDiff_const.sub (contDiff_id.div_const c))

theorem deriv_prof (c : ℝ) :
    deriv (prof c) = fun u => -(1 / c) * deriv Real.smoothTransition (2 - u / c) := by
  funext u
  have h1 := ((contDiff_tau.differentiable (by simp)) (2 - u / c)).hasDerivAt
  exact (h1.comp u (hasDerivAt_inner c u)).deriv.trans (by ring)

theorem deriv2_prof (c : ℝ) :
    deriv (deriv (prof c)) = fun u => (1 / c) ^ 2 * deriv (deriv Real.smoothTransition) (2 - u / c) := by
  rw [deriv_prof]
  funext u
  have h1 := ((contDiff_tau'.differentiable (by simp)) (2 - u / c)).hasDerivAt
  exact ((h1.comp u (hasDerivAt_inner c u)).const_mul (-(1 / c))).deriv.trans (by ring)

theorem notMem_Icc_of {c u : ℝ} (hc : 0 < c) (hu : u ∉ Set.Icc c (2 * c)) :
    2 - u / c ∉ Set.Icc (0 : ℝ) 1 := by
  rintro ⟨h0, h1⟩
  refine hu ⟨?_, ?_⟩
  · have : 1 ≤ u / c := by linarith
    exact (one_le_div hc).mp this
  · have : u / c ≤ 2 := by linarith
    exact (div_le_iff₀ hc).mp this

theorem integral_comp_aff (f : ℝ → ℝ) {c : ℝ} (hc : 0 < c) :
    ∫ u, f (2 - u / c) = c * ∫ w, f w := by
  have h1 := Measure.integral_comp_div (fun w => f (2 - w)) c
  have h2 := integral_sub_left_eq_self f volume (2 : ℝ)
  rw [h1, h2, abs_of_pos hc, smul_eq_mul]

section Sheets

variable {n e : ℕ} {I : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin (e + 1)) (Fin n) ℂ}

theorem sheetSum_nonneg (F : (Fin n → ℂ) → ((Fin (e + 1) → ℂ) → Fin n → ℂ) → ℝ) (y : Fin (e + 1) → ℂ)
    (hF : ∀ x s, 0 ≤ F x s) : 0 ≤ sheetSum I A F y := by
  unfold sheetSum
  refine finsum_nonneg fun x => finsum_nonneg fun _ => ?_
  split_ifs
  · exact hF _ _
  · exact le_rfl

theorem sheet_terms (hchain : MaDensChain.Statement) (c : ℝ) (L : (Fin n → ℂ) → ℝ)
    (hL : SmoothNear (zeroSet I) L) {x : Fin n → ℂ} {y : Fin (e + 1) → ℂ}
    {s : (Fin (e + 1) → ℂ) → Fin n → ℂ} (hx : x ∈ fibre I A y) (hs : IsSheetAt I A x s) :
    maDens (fun k => (vecCons (prof c ∘ L) fun _ => L : Fin (e + 1) → (Fin n → ℂ) → ℝ) k ∘ s) y =
        deriv (prof c) (L x) * maDens (fun k => (fun _ => L : Fin (e + 1) → (Fin n → ℂ) → ℝ) k ∘ s) y +
          deriv (deriv (prof c)) (L x) * gradDens (fun _ : Fin e => L ∘ s) (L ∘ s) (L ∘ s) y ∧
      maDens (fun k => (vecCons (fun x => (prof c ∘ L) x ^ 2 / 2) fun _ => L :
            Fin (e + 1) → (Fin n → ℂ) → ℝ) k ∘ s) y -
          (prof c ∘ L) x * maDens (fun k => (vecCons (prof c ∘ L) fun _ => L :
            Fin (e + 1) → (Fin n → ℂ) → ℝ) k ∘ s) y =
        deriv (prof c) (L x) ^ 2 * gradDens (fun _ : Fin e => L ∘ s) (L ∘ s) (L ∘ s) y := by
  obtain ⟨-, rfl⟩ := hx
  have hsx : s (A *ᵥ x) = x := hs.choose_spec.2.2.2.1
  have hG : ContDiffAt ℝ 2 (L ∘ s) (A *ᵥ x) := StokesOffDiscriminant.contDiffAt_comp_sheet hL hs
  have hF : ContDiff ℝ 2 (prof c) := (contDiff_prof c).of_le (WithTop.coe_le_coe.mpr le_top)
  have hFG : ContDiffAt ℝ 2 (prof c ∘ (L ∘ s)) (A *ᵥ x) := hF.contDiffAt.comp _ hG
  have hcons : (fun k => (fun _ => L : Fin (e + 1) → (Fin n → ℂ) → ℝ) k ∘ s) =
      Fin.cons (L ∘ s) (fun _ : Fin e => L ∘ s) := by
    funext k
    exact Fin.cases rfl (fun _ => rfl) k
  have hch := hchain e (fun _ => L ∘ s) (prof c) (L ∘ s) (A *ᵥ x) hF hG
  have hle := (MaDensLeibniz.proof e (fun _ => L ∘ s) (prof c ∘ (L ∘ s)) (prof c ∘ (L ∘ s)) (A *ᵥ x)
    hFG hFG).2
  have hLx : (L ∘ s) (A *ᵥ x) = L x := by simp [hsx]
  rw [hLx] at hch
  rw [vecCons_comp, vecCons_comp, hcons]
  have e1 : (prof c ∘ L) ∘ s = prof c ∘ (L ∘ s) := rfl
  have e2 : (fun x => (prof c ∘ L) x ^ 2 / 2) ∘ s = fun y => (prof c ∘ (L ∘ s)) y ^ 2 / 2 := rfl
  have e3 : (prof c ∘ L) x = (prof c ∘ (L ∘ s)) (A *ᵥ x) := by simp [hsx]
  rw [e1, e2, e3, hle, hch.1, hch.2]
  constructor <;> ring

end Sheets

def w₂ (c : ℝ) : ℝ → ℝ := deriv (deriv (prof c))

def w₁ (c : ℝ) (u : ℝ) : ℝ := deriv (prof c) u ^ 2

theorem w₂_eq (c : ℝ) :
    w₂ c = fun u => (1 / c) ^ 2 * deriv (deriv Real.smoothTransition) (2 - u / c) :=
  deriv2_prof c

theorem w₁_eq (c : ℝ) :
    w₁ c = fun u => (1 / c) ^ 2 * deriv Real.smoothTransition (2 - u / c) ^ 2 := by
  funext u
  rw [w₁, deriv_prof]
  ring

theorem continuous_w₂ (c : ℝ) : Continuous (w₂ c) := by
  rw [w₂_eq]
  exact continuous_const.mul (contDiff_tau''.continuous.comp (by fun_prop))

theorem continuous_w₁ (c : ℝ) : Continuous (w₁ c) := by
  rw [w₁_eq]
  exact continuous_const.mul ((contDiff_tau'.continuous.comp (by fun_prop)).pow 2)

theorem hasCompactSupport_w₂ {c : ℝ} (hc : 0 < c) : HasCompactSupport (w₂ c) := by
  rw [w₂_eq]
  exact HasCompactSupport.intro (isCompact_Icc (a := c) (b := 2 * c)) fun u hu => by
    simp [tau''_eq_zero (notMem_Icc_of hc hu)]

theorem hasCompactSupport_w₁ {c : ℝ} (hc : 0 < c) : HasCompactSupport (w₁ c) := by
  rw [w₁_eq]
  exact HasCompactSupport.intro (isCompact_Icc (a := c) (b := 2 * c)) fun u hu => by
    simp [tau'_eq_zero (notMem_Icc_of hc hu)]

theorem integral_abs_w₂ {c : ℝ} (hc : 0 < c) :
    ∫ u, |w₂ c u| = (∫ w, |deriv (deriv Real.smoothTransition) w|) / c := by
  have : ∀ u, |w₂ c u| = (1 / c) ^ 2 * |deriv (deriv Real.smoothTransition) (2 - u / c)| := by
    intro u
    rw [w₂_eq, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 / c) ^ 2)]
  simp_rw [this]
  rw [integral_const_mul, integral_comp_aff (fun w => |deriv (deriv Real.smoothTransition) w|) hc]
  field_simp

theorem integral_abs_w₁ {c : ℝ} (hc : 0 < c) :
    ∫ u, |w₁ c u| = (∫ w, |deriv Real.smoothTransition w ^ 2|) / c := by
  have : ∀ u, |w₁ c u| = (1 / c) ^ 2 * |deriv Real.smoothTransition (2 - u / c) ^ 2| := by
    intro u
    rw [w₁_eq, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 / c) ^ 2)]
  simp_rw [this]
  rw [integral_const_mul, integral_comp_aff (fun w => |deriv Real.smoothTransition w ^ 2|) hc]
  field_simp

theorem abs_prof_le_one (c u : ℝ) : |prof c u| ≤ 1 := by
  unfold prof
  exact abs_le.mpr ⟨by linarith [Real.smoothTransition.nonneg (2 - u / c)], Real.smoothTransition.le_one _⟩

section Sums

variable {n e : ℕ} {I : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin (e + 1)) (Fin n) ℂ}

theorem mass_pointwise (hchain : MaDensChain.Statement) (hA : IsFiniteProjection I A) (c S : ℝ)
    (hS : ∀ u, |deriv (prof c) u| ≤ S) (L : (Fin n → ℂ) → ℝ) (hL : SmoothNear (zeroSet I) L)
    (y : Fin (e + 1) → ℂ) :
    chartAbsDens I A (fun _ => 1) (vecCons (prof c ∘ L) fun _ => L) y ≤
      S * chartAbsDens I A (fun _ => 1) (fun _ => L) y +
        sheetSum I A (fun x s => |w₂ c (L x) * gradDens (fun _ : Fin e => L ∘ s) (L ∘ s) (L ∘ s) y|) y := by
  have hfin := IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA y
  unfold chartAbsDens
  rw [CutOffDominated.sheetSum_eq_sum _ hfin, CutOffDominated.sheetSum_eq_sum _ hfin,
    CutOffDominated.sheetSum_eq_sum _ hfin, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun x hx => ?_
  rw [Set.Finite.mem_toFinset] at hx
  split_ifs with hs
  · beta_reduce
    rw [one_mul, one_mul, (sheet_terms hchain c L hL hx hs.choose_spec).1]
    refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hS _) (abs_nonneg _)
  · simp

theorem energy_pointwise (hchain : MaDensChain.Statement) (hA : IsFiniteProjection I A) (c : ℝ)
    (L : (Fin n → ℂ) → ℝ) (hL : SmoothNear (zeroSet I) L) (y : Fin (e + 1) → ℂ) :
    |chartDens I A (fun _ => 1) (vecCons (fun x => (prof c ∘ L) x ^ 2 / 2) fun _ => L) y -
        chartDens I A (prof c ∘ L) (vecCons (prof c ∘ L) fun _ => L) y| ≤
      sheetSum I A (fun x s => |w₁ c (L x) * gradDens (fun _ : Fin e => L ∘ s) (L ∘ s) (L ∘ s) y|) y := by
  have hfin := IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA y
  unfold chartDens
  rw [CutOffDominated.sheetSum_eq_sum _ hfin, CutOffDominated.sheetSum_eq_sum _ hfin,
    CutOffDominated.sheetSum_eq_sum _ hfin, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x hx => ?_)
  rw [Set.Finite.mem_toFinset] at hx
  split_ifs with hs
  · beta_reduce
    rw [one_mul, (sheet_terms hchain c L hL hx hs.choose_spec).2]
    exact le_rfl
  · simp

theorem weight_pointwise (hA : IsFiniteProjection I A) (c : ℝ) (L : (Fin n → ℂ) → ℝ) (y : Fin (e + 1) → ℂ) :
    |chartDens I A (prof c ∘ L) (vecCons (prof c ∘ L) fun _ => L) y| ≤
      chartAbsDens I A (fun _ => 1) (vecCons (prof c ∘ L) fun _ => L) y := by
  have hfin := IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA y
  unfold chartDens chartAbsDens
  rw [CutOffDominated.sheetSum_eq_sum _ hfin, CutOffDominated.sheetSum_eq_sum _ hfin]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  split_ifs
  · beta_reduce
    rw [abs_mul, abs_mul, abs_one]
    exact mul_le_mul_of_nonneg_right (abs_prof_le_one c (L x)) (abs_nonneg _)
  · simp

end Sums

section Core

variable {n e : ℕ} {I : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin (e + 1)) (Fin n) ℂ}

theorem core (hchain : MaDensChain.Statement) (hA : IsFiniteProjection I A) (L : (Fin n → ℂ) → ℝ)
    (hL : SmoothNear (zeroSet I) L) (hLm : Measurable L)
    (hMint : Integrable (chartAbsDens I A (fun _ => 1) (fun _ => L)))
    (hLS : ∀ ψ : ℝ → ℝ, Continuous ψ → HasCompactSupport ψ →
      Integrable (fun y => sheetSum I A (fun x s =>
        |ψ (L x) * gradDens (fun _ : Fin e => L ∘ s) (L ∘ s) (L ∘ s) y|) y) ∧
      (∫ y, sheetSum I A (fun x s => |ψ (L x) * gradDens (fun _ : Fin e => L ∘ s) (L ∘ s) (L ∘ s) y|) y) ≤
        (∫ y, chartAbsDens I A (fun _ => 1) (fun _ => L) y) * ∫ r, |ψ r|) :
    ∃ C : ℝ, ∀ k : ℕ,
      (∫ y, chartAbsDens I A (fun _ => 1) (vecCons (prof ((k : ℝ) + 1) ∘ L) fun _ => L) y) ≤
          C / ((k : ℝ) + 1) ∧
        chartInt I A (fun _ => 1) (vecCons (fun x => (prof ((k : ℝ) + 1) ∘ L) x ^ 2 / 2) fun _ => L) -
            chartInt I A (prof ((k : ℝ) + 1) ∘ L) (vecCons (prof ((k : ℝ) + 1) ∘ L) fun _ => L) ≤
          C / ((k : ℝ) + 1) := by
  have hcs1 : HasCompactSupport (deriv Real.smoothTransition) :=
    HasCompactSupport.intro isCompact_Icc fun u hu => tau'_eq_zero hu
  obtain ⟨S₁, hS₁⟩ := contDiff_tau'.continuous.bounded_above_of_compact_support hcs1
  have hS₁0 : 0 ≤ S₁ := (norm_nonneg _).trans (hS₁ 0)
  have hM0 : 0 ≤ ∫ y, chartAbsDens I A (fun _ => 1) (fun _ => L) y :=
    integral_nonneg fun y => sheetSum_nonneg _ y fun _ _ => abs_nonneg _
  have hK₁0 : 0 ≤ ∫ w, |deriv Real.smoothTransition w ^ 2| := integral_nonneg fun _ => abs_nonneg _
  have hK₂0 : 0 ≤ ∫ w, |deriv (deriv Real.smoothTransition) w| := integral_nonneg fun _ => abs_nonneg _
  set M := ∫ y, chartAbsDens I A (fun _ => 1) (fun _ => L) y with hM
  set K₁ := ∫ w, |deriv Real.smoothTransition w ^ 2| with hK₁
  set K₂ := ∫ w, |deriv (deriv Real.smoothTransition) w| with hK₂
  refine ⟨S₁ * M + M * K₂ + M * K₁, fun k => ?_⟩
  set c : ℝ := (k : ℝ) + 1 with hcdef
  have hc : 0 < c := by positivity
  have hSc : ∀ u, |deriv (prof c) u| ≤ S₁ / c := by
    intro u
    rw [deriv_prof, abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 1 / c)]
    have := hS₁ (2 - u / c)
    rw [Real.norm_eq_abs] at this
    calc 1 / c * |deriv Real.smoothTransition (2 - u / c)| ≤ 1 / c * S₁ :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = S₁ / c := by ring
  have hQ := hLS (w₂ c) (continuous_w₂ c) (hasCompactSupport_w₂ hc)
  have hP := hLS (w₁ c) (continuous_w₁ c) (hasCompactSupport_w₁ hc)
  rw [integral_abs_w₂ hc, ← hK₂] at hQ
  rw [integral_abs_w₁ hc, ← hK₁] at hP
  have hχm : Measurable (prof c ∘ L) := (contDiff_prof c).continuous.measurable.comp hLm
  have hm_meas : Measurable (chartAbsDens I A (fun _ => 1) (vecCons (prof c ∘ L) fun _ => L)) :=
    SheetSumMeasurable.measurable_sheetSum hA (fun u m => |u * m|)
      (continuous_fst.mul continuous_snd).abs.measurable measurable_const _
  have hbd_int := (hMint.const_mul (S₁ / c)).add hQ.1
  have hm_int : Integrable (chartAbsDens I A (fun _ => 1) (vecCons (prof c ∘ L) fun _ => L)) :=
    hbd_int.mono' hm_meas.aestronglyMeasurable (ae_of_all _ fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by unfold chartAbsDens; exact sheetSum_nonneg _ y fun _ _ => abs_nonneg _)]
      exact mass_pointwise hchain hA c (S₁ / c) hSc L hL y)
  have hfin : (S₁ * M + M * K₂ + M * K₁) / c = S₁ / c * M + M * (K₂ / c) + M * (K₁ / c) := by ring
  have hK₁c : 0 ≤ M * (K₁ / c) := mul_nonneg hM0 (div_nonneg hK₁0 hc.le)
  have hK₂c : 0 ≤ S₁ / c * M + M * (K₂ / c) :=
    add_nonneg (mul_nonneg (div_nonneg hS₁0 hc.le) hM0) (mul_nonneg hM0 (div_nonneg hK₂0 hc.le))
  constructor
  · calc (∫ y, chartAbsDens I A (fun _ => 1) (vecCons (prof c ∘ L) fun _ => L) y)
        ≤ ∫ y, (S₁ / c * chartAbsDens I A (fun _ => 1) (fun _ => L) y +
            sheetSum I A (fun x s => |w₂ c (L x) * gradDens (fun _ : Fin e => L ∘ s) (L ∘ s) (L ∘ s) y|) y) :=
          integral_mono hm_int hbd_int fun y => mass_pointwise hchain hA c (S₁ / c) hSc L hL y
      _ = S₁ / c * M + ∫ y, sheetSum I A
            (fun x s => |w₂ c (L x) * gradDens (fun _ : Fin e => L ∘ s) (L ∘ s) (L ∘ s) y|) y := by
          rw [integral_add (hMint.const_mul _) hQ.1, integral_const_mul]
      _ ≤ S₁ / c * M + M * (K₂ / c) := by linarith [hQ.2]
      _ ≤ (S₁ * M + M * K₂ + M * K₁) / c := by rw [hfin]; linarith
  · have ha_meas : Measurable
        (chartDens I A (fun _ => 1) (vecCons (fun x => (prof c ∘ L) x ^ 2 / 2) fun _ => L)) :=
      SheetSumMeasurable.measurable_sheetSum hA (fun u m => u * m)
        (continuous_fst.mul continuous_snd).measurable measurable_const _
    have hb_meas : Measurable (chartDens I A (prof c ∘ L) (vecCons (prof c ∘ L) fun _ => L)) :=
      SheetSumMeasurable.measurable_sheetSum hA (fun u m => u * m)
        (continuous_fst.mul continuous_snd).measurable hχm _
    have hb_int : Integrable (chartDens I A (prof c ∘ L) (vecCons (prof c ∘ L) fun _ => L)) :=
      hm_int.mono' hb_meas.aestronglyMeasurable (ae_of_all _ fun y => by
        rw [Real.norm_eq_abs]
        exact weight_pointwise hA c L y)
    have hab_int : Integrable fun y =>
        chartDens I A (fun _ => 1) (vecCons (fun x => (prof c ∘ L) x ^ 2 / 2) fun _ => L) y -
          chartDens I A (prof c ∘ L) (vecCons (prof c ∘ L) fun _ => L) y :=
      hP.1.mono' (ha_meas.sub hb_meas).aestronglyMeasurable (ae_of_all _ fun y => by
        rw [Real.norm_eq_abs]
        exact energy_pointwise hchain hA c L hL y)
    have ha_int : Integrable
        (chartDens I A (fun _ => 1) (vecCons (fun x => (prof c ∘ L) x ^ 2 / 2) fun _ => L)) :=
      (hab_int.add hb_int).congr (ae_of_all _ fun y => by simp)
    unfold chartInt
    rw [← integral_sub ha_int hb_int]
    calc _ ≤ ∫ y, sheetSum I A
            (fun x s => |w₁ c (L x) * gradDens (fun _ : Fin e => L ∘ s) (L ∘ s) (L ∘ s) y|) y :=
          integral_mono hab_int hP.1 fun y => (le_abs_self _).trans (energy_pointwise hchain hA c L hL y)
      _ ≤ M * (K₁ / c) := hP.2
      _ ≤ (S₁ * M + M * K₂ + M * K₁) / c := by rw [hfin]; linarith

end Core

theorem proof (h₁ : MaDensChain.Statement) (h₂ : SliceLevelSet.Statement) (h₃ : SliceMassFinite.Statement) :
    SliceCutDecay.Statement := by
  intro n e h W g ℓ A hW hg hℓ hA
  obtain ⟨hIp, hIdim, -⟩ := SliceIdeal.proof n (e + 1) W g ℓ hW hg hℓ
  have hMint := h₃ n (e + 1) h (W ⊔ Ideal.span {linForm ℓ - 1}) ℓ A hIp
    (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)) hIdim hA
  obtain ⟨C, hC⟩ := core h₁ hA (fun x => Real.log (h.dualNorm x)) (smoothNear_log_dualNorm_slice h W ℓ)
    (Real.measurable_log.comp (SliceCut.continuous_dualNorm h).measurable) hMint
    (fun ψ hψ hψs => h₂ n e h W g ℓ A ψ hW hg hℓ hA hψ hψs)
  exact ⟨C, hC⟩

end SliceCutDecay

end

end GroundTheory.Heights₂.Heights
