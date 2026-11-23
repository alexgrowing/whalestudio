import ReciprocityTheory.L2DbarEstimates.NormFibrations.Hormander
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.ChartSymmEventuallyEq
import ReciprocityTheory.L2DbarEstimates.LeviForms.EventuallyDifferentiableAtOfContDiffAt

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.HE

open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal

noncomputable section

variable {n : ℕ} {U : Set (V n)}

theorem val_lh (hU : IsOpen U) : IsLocalHomeomorph (Subtype.val : U → V n) :=
  hU.isOpenEmbedding_subtypeVal.isLocalHomeomorph

theorem symm_val {e : OpenPartialHomeomorph U (V n)} (he : IsChart n (Subtype.val : U → V n) e)
    {y : V n} (hy : y ∈ e.target) : ((e.symm y : U) : V n) = y :=
  (he (e.map_target hy)).trans (e.right_inv hy)

theorem target_sub {e : OpenPartialHomeomorph U (V n)} (he : IsChart n (Subtype.val : U → V n) e) :
    e.target ⊆ U := fun y hy => by
  rw [← symm_val he hy]
  exact (e.symm y).2

theorem comp_symm_eqOn (f : V n → ℂ) {e : OpenPartialHomeomorph U (V n)}
    (he : IsChart n (Subtype.val : U → V n) e) :
    Set.EqOn ((fun x : U => f x.1) ∘ e.symm) f e.target := fun y hy => by
  simp only [Function.comp]
  rw [symm_val he hy]

theorem smooth_val {f : V n → ℂ} (hf : ContDiffOn ℝ ∞ f U) :
    Smooth n (Subtype.val : U → V n) (fun x => f x.1) := fun e he =>
  (hf.mono (target_sub he)).congr (comp_symm_eqOn f he)

theorem smoothR_val {f : V n → ℝ} (hf : ContDiffOn ℝ ∞ f U) :
    SmoothR n (Subtype.val : U → V n) (fun x => f x.1) :=
  smooth_val (f := fun y => (f y : ℂ)) (Complex.ofRealCLM.contDiff.comp_contDiffOn hf)

theorem eventually_target (hU : IsOpen U) {e : OpenPartialHomeomorph U (V n)}
    (he : IsChart n (Subtype.val : U → V n) e) {x : U} (hx : x ∈ e.source) :
    e.target ∈ 𝓝 x.1 := by
  have hx' : x.1 ∈ e.target := by
    rw [show x.1 = e x from he hx]
    exact e.map_source hx
  exact e.open_target.mem_nhds hx'

theorem levi_val (hU : IsOpen U) (f : V n → ℝ) (x : U) (ξ : Fin n → ℂ) :
    Levi n (Subtype.val : U → V n) (fun y => f y.1) x ξ = leviV n (fun y => (f y : ℂ)) x.1 ξ := by
  obtain ⟨e, he, hx⟩ := exists_chart n (Subtype.val : U → V n) (val_lh hU) x
  rw [levi_eq_leviV n _ e he _ x hx ξ]
  exact leviV_congr ((comp_symm_eqOn (fun y => (f y : ℂ)) he).eventuallyEq_of_mem
    (eventually_target hU he hx)) ξ

theorem db_val (hU : IsOpen U) (f : V n → ℂ) (j : Fin n) (x : U) :
    db n (Subtype.val : U → V n) j (fun y => f y.1) x = wdb n j f x.1 := by
  obtain ⟨e, he, hx⟩ := exists_chart n (Subtype.val : U → V n) (val_lh hU) x
  rw [db_eq_wdb n _ e he j _ x hx]
  have hfe : ((fun y : U => f y.1) ∘ e.symm) =ᶠ[𝓝 x.1] f :=
    (comp_symm_eqOn f he).eventuallyEq_of_mem (eventually_target hU he hx)
  simp only [wdb]
  rw [hfe.fderiv_eq]

def ext0 (F : U → ℂ) (y : V n) : ℂ := by
  classical
  exact if h : y ∈ U then F ⟨y, h⟩ else 0

theorem extendByZeroOnSubset_apply_coe (F : U → ℂ) (x : U) : ext0 F x.1 = F x := by
  simp [ext0, x.2]

theorem differentiableOn_extendByZero (hU : IsOpen U) {F : U → ℂ} (hF : Holo n (Subtype.val : U → V n) F) :
    DifferentiableOn ℂ (ext0 F) U := by
  intro y hy
  obtain ⟨e, he, hx⟩ := exists_chart n (Subtype.val : U → V n) (val_lh hU) ⟨y, hy⟩
  have hT : e.target ∈ 𝓝 y := eventually_target hU he hx
  have hd : DifferentiableAt ℂ (F ∘ e.symm) y := (hF e he).differentiableAt hT
  have heq : (F ∘ e.symm) =ᶠ[𝓝 y] ext0 F := by
    refine Filter.eventuallyEq_of_mem hT fun w hw => ?_
    have h1 := extendByZeroOnSubset_apply_coe F (e.symm w)
    rw [symm_val he hw] at h1
    exact h1.symm
  exact (hd.congr_of_eventuallyEq heq.symm).differentiableWithinAt

private theorem volFun_val_eq_volume_image (hU : IsOpen U) (A : Set U) (hA : MeasurableSet A) :
    volFun n (Subtype.val : U → V n) A = volume (Subtype.val '' A) := by
  have key : ∀ y : V n, ((A ∩ Subtype.val ⁻¹' {y}).encard : ℝ≥0∞) =
      (Subtype.val '' A).indicator 1 y := by
    intro y
    by_cases hy : y ∈ Subtype.val '' A
    · obtain ⟨x, hxA, rfl⟩ := hy
      have hs : A ∩ Subtype.val ⁻¹' {x.1} = {x} := by
        ext z
        constructor
        · rintro ⟨-, hz⟩
          exact Set.mem_singleton_iff.mpr (Subtype.ext (Set.mem_singleton_iff.mp hz))
        · intro hz
          rw [Set.mem_singleton_iff] at hz
          subst hz
          exact ⟨hxA, rfl⟩
      rw [hs, Set.encard_singleton, Set.indicator_of_mem (Set.mem_image_of_mem _ hxA)]
      simp
    · have hs : A ∩ Subtype.val ⁻¹' {y} = ∅ := by
        ext z
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false,
          iff_false, not_and]
        intro hz hzy
        exact hy ⟨z, hz, hzy⟩
      rw [hs, Set.encard_empty]
      simp [Set.indicator, hy]
  rw [volFun, lintegral_congr key, lintegral_indicator_one (hU.measurableSet.subtype_image hA)]

theorem vol_val (hU : IsOpen U) :
    vol n (Subtype.val : U → V n) = Measure.comap Subtype.val volume := by
  have hadd : VolAdditive n (Subtype.val : U → V n) := by
    intro f hf hd
    rw [volFun_val_eq_volume_image hU _ (MeasurableSet.iUnion hf), Set.image_iUnion]
    rw [measure_iUnion (fun i j hij => (hd hij).image Subtype.val_injective.injOn
      (Set.subset_univ _) (Set.subset_univ _)) (fun i => hU.measurableSet.subtype_image (hf i))]
    exact tsum_congr fun i => (volFun_val_eq_volume_image hU _ (hf i)).symm
  ext A hA
  rw [vol, dif_pos hadd, Measure.ofMeasurable_apply _ hA,
    Measure.comap_apply _ Subtype.val_injective (fun s hs => hU.measurableSet.subtype_image hs) _ hA]
  exact volFun_val_eq_volume_image hU A hA

theorem lintegral_val (hU : IsOpen U) (g : V n → ℝ≥0∞) :
    ∫⁻ x, g x.1 ∂vol n (Subtype.val : U → V n) = ∫⁻ y in U, g y := by
  rw [vol_val hU]
  exact lintegral_subtype_comap hU.measurableSet g

theorem hormander_open (hU : IsOpen U) (e : V n → ℝ) (he : ContDiffOn ℝ ∞ e U)
    (hel : ∀ y ∈ U, ∀ ξ : Fin n → ℂ, 0 ≤ (leviV n (fun w => (e w : ℂ)) y ξ).re)
    (hec : ∀ a : ℝ, IsCompact {y | y ∈ U ∧ e y ≤ a})
    (φ : V n → ℝ) (hφ : ContDiffOn ℝ ∞ φ U)
    (hφl : ∀ y ∈ U, ∀ ξ : Fin n → ℂ, 0 ≤ (leviV n (fun w => (φ w : ℂ)) y ξ).re)
    (F0 : V n → ℂ) (hF0 : ContDiffOn ℝ ∞ F0 U) (h : V n → ℝ≥0∞) (hh : Measurable h)
    (hb : ∀ y ∈ U, ∀ ξ : Fin n → ℂ,
      ENNReal.ofReal (‖∑ j, wdb n j F0 y * (starRingEnd ℂ) (ξ j)‖ ^ 2) ≤
        h y * ENNReal.ofReal (leviV n (fun w => (φ w : ℂ)) y ξ).re) :
    ∃ F : V n → ℂ, DifferentiableOn ℂ F U ∧
      ∫⁻ y in U, ENNReal.ofReal (‖F0 y - F y‖ ^ 2 * Real.exp (-φ y)) ≤
        ∫⁻ y in U, h y * ENNReal.ofReal (Real.exp (-φ y)) := by
  let X : EtaleStein n U :=
    { z := Subtype.val
      isLocalHomeomorph := val_lh hU
      e := fun x => e x.1
      smooth_e := smoothR_val he
      levi_e := fun x ξ => by rw [levi_val hU]; exact hel x.1 x.2 ξ
      isCompact_le := fun a => by
        rw [Subtype.isCompact_iff]
        convert hec a using 1
        ext y
        simp [and_comm] }
  obtain ⟨F, hFh, hFi⟩ := ReciprocityTheory.L2DbarEstimates.hormander n U X (fun x => φ x.1) (fun x => F0 x.1)
    (fun x => h x.1) (smoothR_val hφ) (fun x ξ => by rw [levi_val hU]; exact hφl x.1 x.2 ξ)
    (smooth_val hF0) (hh.comp measurable_subtype_coe) (fun x ξ => by
      show ENNReal.ofReal (‖dbarDot n (Subtype.val : U → V n) (fun x => F0 x.1) x ξ‖ ^ 2) ≤
        h x.1 * ENNReal.ofReal (Levi n (Subtype.val : U → V n) (fun x => φ x.1) x ξ).re
      rw [levi_val hU, dbarDot]
      simp only [db_val hU]
      exact hb x.1 x.2 ξ)
  refine ⟨ext0 F, differentiableOn_extendByZero hU hFh, ?_⟩
  have e1 : ∫⁻ y in U, ENNReal.ofReal (‖F0 y - ext0 F y‖ ^ 2 * Real.exp (-φ y)) =
      wint n (Subtype.val : U → V n) (fun x => F0 x.1 - F x) (fun x => φ x.1) := by
    rw [wint, ← lintegral_val hU]
    refine lintegral_congr fun x => ?_
    simp only [extendByZeroOnSubset_apply_coe]
  have e2 : ∫⁻ y in U, h y * ENNReal.ofReal (Real.exp (-φ y)) =
      ∫⁻ x, h x.1 * ENNReal.ofReal (Real.exp (-φ x.1)) ∂vol n (Subtype.val : U → V n) :=
    (lintegral_val hU _).symm
  rw [e1, e2]
  exact hFi

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.HE
