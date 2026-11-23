import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDegreeDensityPullbackEqNormSqDetMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFormMul
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.IntegralFderivApplyEqZero

set_option autoImplicit false

noncomputable section

open Set Filter Topology Matrix MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)
open scoped ContDiff ComplexOrder

namespace GlobalTheory.CxForm.LocStokes

open GlobalTheory.CxForm

variable {n : ℕ}

theorem dens_zero : dens (0 : Alt n) = 0 := by simp [dens]

theorem delAt_eq_zero_of_eventually {F : V n → Alt n} {v : V n} (h : F =ᶠ[𝓝 v] fun _ => 0) : delAt F v = 0 := by
  have hS : ∀ S, GlobalTheory.del (fun x => (bas n).repr (F x) S) v = 0 := fun S => by
    have e : (fun x => (bas n).repr (F x) S) =ᶠ[𝓝 v] fun _ => 0 := h.mono fun x hx => by simp [hx]
    rw [GlobalTheory.del_congr e]
    exact GlobalTheory.del_const _ _
  simp [delAt, coefwise, hS]

theorem del_integral {f : V n → ℂ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) (u : V n) :
    Integrable (fun v => GlobalTheory.del f v u) ∧ ∫ v, GlobalTheory.del f v u = 0 := by
  have hint : ∀ w : V n, Integrable (fun y => fderiv ℝ f y w) := fun w =>
    ((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hc.fderiv_apply (𝕜 := ℝ) w)
  have hD : Integrable (fun v => GlobalTheory.del f v u) := by
    simp only [GlobalTheory.del_apply, smul_eq_mul]
    exact ((hint _).sub ((hint _).const_mul _)).const_mul _
  refine ⟨hD, ?_⟩
  simp only [GlobalTheory.del_apply, smul_eq_mul]
  rw [integral_const_mul, integral_sub (hint _) ((hint _).const_mul _), integral_const_mul,
    ReciprocityTheory.L2DbarEstimates.integral_fderiv_apply_eq_zero n f hf hc, ReciprocityTheory.L2DbarEstimates.integral_fderiv_apply_eq_zero n f hf hc]
  simp

theorem dens_delAt (F : V n → Alt n) (v : V n) : dens (delAt F v) =
    ∑ a, ∑ S, GlobalTheory.del (fun x => (bas n).repr (F x) S) v (coordVec a) *
      ((bas n).repr (dz a * bas n S) Finset.univ / (bas n).repr (vol n : Alt n) Finset.univ) := by
  simp only [dens, delAt, coefwise, Finset.mul_sum, mul_smul_comm, map_sum, map_smul, Finsupp.coe_finset_sum,
    Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, Finset.sum_div, mul_div_assoc]

theorem integral_dens_delAt {F : V n → Alt n} (hF : ∀ S, ContDiff ℝ 1 fun v => (bas n).repr (F v) S)
    (hc : ∀ S, HasCompactSupport fun v => (bas n).repr (F v) S) :
    Integrable (fun v => dens (delAt F v)) ∧ ∫ v, dens (delAt F v) = 0 := by
  have hi : ∀ a S, Integrable fun v => GlobalTheory.del (fun x => (bas n).repr (F x) S) v (coordVec a) *
      ((bas n).repr (dz a * bas n S) Finset.univ / (bas n).repr (vol n : Alt n) Finset.univ) :=
    fun a S => (del_integral (hF S) (hc S) _).1.mul_const _
  simp only [dens_delAt]
  refine ⟨integrable_finset_sum _ fun a _ => integrable_finset_sum _ fun S _ => hi a S, ?_⟩
  rw [integral_finset_sum _ fun a _ => integrable_finset_sum _ fun S _ => hi a S]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [integral_finset_sum _ fun S _ => hi a S]
  refine Finset.sum_eq_zero fun S _ => ?_
  rw [integral_mul_const, (del_integral (hF S) (hc S) _).2, zero_mul]

end GlobalTheory.CxForm.LocStokes

namespace GlobalTheory.CxForm.LocStokes

open GlobalTheory.CxForm

variable {n : ℕ}

theorem integral_eq_of_vanish {M : Type} [TopologicalSpace M] [SecondCountableTopology M] [MeasurableSpace M]
    [BorelSpace M] (A : HolAtlas M n) {α : A.Fld} (hα : A.IsForm α) (i : A.ι) {K : Set M} (hKm : MeasurableSet K)
    (hKs : K ⊆ (A.e i).source) (h0 : ∀ x : A.Pt, x.pt ∉ K → α x = 0)
    (hI : Integrable fun v => (dens (A.loc α i v)).re) :
    A.integral α = ∫ v, (dens (A.loc α i v)).re := by
  have hl : ∀ j y (hy : y ∈ (A.e j).source), A.loc α j (A.e j y) = α ⟨(j, y), hy⟩ := fun j y hy =>
    A.loc_crd α ⟨(j, y), hy⟩
  have hρ : ∀ (ε : ℤˣ) j k y, y ∈ (A.e j).source → y ∈ (A.e k).source →
      ENNReal.ofReal ((ε : ℤ) * (dens (A.loc α j (A.e j y))).re) =
      ENNReal.ofReal (‖ChartGlue.transDet (A.e j) (A.e k) y‖ ^ 2) *
        ENNReal.ofReal ((ε : ℤ) * (dens (A.loc α k (A.e k y))).re) := by
    intro ε j k y hj hk
    rw [hl j y hj, hl k y hk, hα.compat ⟨(j, y), hj⟩ ⟨(k, y), hk⟩ rfl, dens_pull,
      ← ENNReal.ofReal_mul (sq_nonneg _)]
    congr 1
    simp only [ChartGlue.transDet, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    ring
  have hz : ∀ (ε : ℤˣ) j y, y ∈ (A.e j).source → y ∉ K →
      ENNReal.ofReal ((ε : ℤ) * (dens (A.loc α j (A.e j y))).re) = 0 := by
    intro ε j y hy hyK
    rw [hl j y hy, h0 ⟨(j, y), hy⟩ hyK, dens_zero]
    simp
  have hc : ∀ ε : ℤˣ, A.part α ε Kᶜ = 0 := fun ε => by
    have key : A.part α ε ≤ (A.part α ε).restrict K := iSup_le fun j => by
      have e : ChartGlue.chartMeas (A.e j)
          (fun y => ENNReal.ofReal ((ε : ℤ) * (dens (A.loc α j (A.e j y))).re)) Kᶜ = 0 := by
        rw [ChartGlue.chartMeas_apply _ _ hKm.compl]
        refine setLIntegral_eq_zero (ChartGlue.measurableSet_image _
          ((A.e j).open_source.measurableSet.inter hKm.compl) Set.inter_subset_left) ?_
        rintro _ ⟨y, hy, rfl⟩
        simp only [(A.e j).left_inv hy.1]
        exact hz ε j y hy.1 hy.2
      rw [← Measure.restrict_eq_self_of_ae_mem (s := K) (mem_ae_iff.2 e)]
      exact Measure.restrict_mono le_rfl (le_iSup (fun j => ChartGlue.chartMeas (A.e j)
        fun y => ENNReal.ofReal ((ε : ℤ) * (dens (A.loc α j (A.e j y))).re)) j)
    refine le_antisymm ((key Kᶜ).trans_eq ?_) bot_le
    rw [Measure.restrict_apply hKm.compl, Set.compl_inter_self, measure_empty]
  have hv : ∀ v, v ∉ (A.e i) '' K → (dens (A.loc α i v)).re = 0 := fun v hv => by
    by_cases ht : v ∈ (A.e i).target
    · rw [HolAtlas.loc, dif_pos ht, h0 ⟨(i, (A.e i).symm v), (A.e i).map_target ht⟩
        fun h => hv ⟨_, h, (A.e i).right_inv ht⟩, dens_zero, Complex.zero_re]
    · rw [HolAtlas.loc, dif_neg ht, dens_zero, Complex.zero_re]
  have hp : ∀ ε : ℤˣ, A.part α ε univ = ∫⁻ v, ENNReal.ofReal ((ε : ℤ) * (dens (A.loc α i v)).re) := fun ε => by
    rw [← measure_add_measure_compl hKm, hc ε, add_zero, HolAtlas.part,
      ChartGlue.glueMeas_apply A.e _ (fun j k => A.holo j k) (hρ ε) i hKm hKs,
      ChartGlue.chartMeas_apply_of_subset _ _ hKm hKs,
      ← lintegral_indicator (ChartGlue.measurableSet_image _ hKm hKs)]
    refine lintegral_congr fun v => ?_
    by_cases hvK : v ∈ (A.e i) '' K
    · obtain ⟨y, hy, rfl⟩ := hvK
      rw [Set.indicator_of_mem (Set.mem_image_of_mem _ hy), (A.e i).left_inv (hKs hy)]
    · rw [Set.indicator_of_notMem hvK, hv v hvK, mul_zero, ENNReal.ofReal_zero]
  rw [HolAtlas.integral, measureReal_def, measureReal_def, hp, hp,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hI]
  simp

end GlobalTheory.CxForm.LocStokes

namespace GlobalTheory.CxForm.LocStokes

open GlobalTheory.CxForm

variable {n : ℕ}

theorem integral_del_fn_mul_eq_zero_of_isForm {M : Type} [TopologicalSpace M] [CompactSpace M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (A : HolAtlas M n) (γ : A.Fld) (χ : M → ℝ)
    (i : A.ι) (hγ : A.IsForm γ) (hχ : A.SmoothOn univ (fun y => (χ y : ℂ))) (hs : tsupport χ ⊆ (A.e i).source)
    (hd : A.IsForm (A.del (A.fn χ * γ))) : A.integral (A.del (A.fn χ * γ)) = 0 := by
  set β : A.Fld := A.fn χ * γ with hβdef
  set K : Set M := tsupport χ with hKdef
  have hKc : IsCompact K := (isClosed_tsupport χ).isCompact
  have hKm : MeasurableSet K := (isClosed_tsupport χ).measurableSet
  have hβ : A.IsForm β := FormMul.isForm_mul A _ _ (A.isForm_fn hχ) hγ
  have hβ0 : ∀ x : A.Pt, x.pt ∉ K → β x = 0 := fun x hx => by
    simp [hβdef, HolAtlas.fn, image_eq_zero_of_notMem_tsupport hx]

  have hβn : ∀ j, ∀ y ∈ (A.e j).source, y ∉ K → A.loc β j =ᶠ[𝓝 (A.e j y)] fun _ => 0 := fun j y hy hyK => by
    filter_upwards [(ChartGlue.isOpen_over (A.e j) (isClosed_tsupport χ).isOpen_compl).mem_nhds
      (ChartGlue.mem_over (A.e j) (S := Kᶜ) hy hyK)] with w hw
    rw [HolAtlas.loc, dif_pos hw.1]
    exact hβ0 _ hw.2
  have hd0 : ∀ x : A.Pt, x.pt ∉ K → A.del β x = 0 := fun x hx =>
    delAt_eq_zero_of_eventually (hβn x.1.1 x.pt x.2 hx)

  set F : V n → Alt n := A.loc β i with hFdef
  set AK : Set (V n) := (A.e i) '' K with hAKdef
  have hAK : IsCompact AK := hKc.image_of_continuousOn ((A.e i).continuousOn.mono hs)
  have hAKt : AK ⊆ (A.e i).target := by
    rintro _ ⟨y, hy, rfl⟩
    exact (A.e i).map_source (hs hy)
  have hF0 : ∀ v ∉ AK, F v = 0 := fun v hv => by
    by_cases ht : v ∈ (A.e i).target
    · rw [hFdef, HolAtlas.loc, dif_pos ht]
      exact hβ0 _ fun h => hv ⟨_, h, (A.e i).right_inv ht⟩
    · rw [hFdef, HolAtlas.loc, dif_neg ht]
  have hFA : ∀ v ∉ AK, F =ᶠ[𝓝 v] fun _ => 0 := fun v hv => by
    filter_upwards [hAK.isClosed.isOpen_compl.mem_nhds hv] with w hw
    exact hF0 w hw
  have hFS : ∀ S, ContDiff ℝ 1 fun v => (bas n).repr (F v) S := fun S => contDiff_iff_contDiffAt.2 fun v => by
    by_cases ht : v ∈ (A.e i).target
    · exact ((hβ.smooth i S).contDiffAt ((A.e i).open_target.mem_nhds ht)).of_le (by simp)
    · refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ((hFA v fun h => ht (hAKt h)).mono fun w hw => ?_)
      simp [hw]
  have hFc : ∀ S, HasCompactSupport fun v => (bas n).repr (F v) S := fun S =>
    HasCompactSupport.intro hAK fun v hv => by simp [hF0 v hv]
  have hloc : ∀ v, A.loc (A.del β) i v = delAt F v := fun v => by
    by_cases ht : v ∈ (A.e i).target
    · rw [HolAtlas.loc, dif_pos ht]
      show delAt (A.loc β i) ((A.e i) ((A.e i).symm v)) = _
      rw [(A.e i).right_inv ht]
    · rw [HolAtlas.loc, dif_neg ht]
      exact (delAt_eq_zero_of_eventually (hFA v fun h => ht (hAKt h))).symm
  obtain ⟨hI, h0⟩ := integral_dens_delAt hFS hFc
  have hIre : Integrable fun v => (dens (A.loc (A.del β) i v)).re := by
    simp only [hloc]
    exact Complex.reCLM.integrable_comp hI
  rw [integral_eq_of_vanish A hd i hKm hs hd0 hIre]
  simp only [hloc]
  have := Complex.reCLM.integral_comp_comm hI
  simp only [Complex.reCLM_apply] at this
  rw [this, h0, Complex.zero_re]

end GlobalTheory.CxForm.LocStokes
