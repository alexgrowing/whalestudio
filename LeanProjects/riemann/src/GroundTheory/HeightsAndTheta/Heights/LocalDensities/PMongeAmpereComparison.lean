import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.Statements
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import ReciprocityTheory.AnalyticForms.PotentialTheory.MaMeasureB
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffOnFubiniStudyProfileInvNormSqFirst
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FourB

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal

noncomputable section

namespace MongeAmpereComparison

def cutoff (t : ℝ) : ℝ := ∫ u in (0 : ℝ)..t, Real.smoothTransition u

theorem hasDerivAt_cutoff (t : ℝ) : HasDerivAt cutoff (Real.smoothTransition t) t :=
  (Real.smoothTransition.continuous.integral_hasStrictDerivAt 0 t).hasDerivAt

theorem contDiff_cutoff : ContDiff ℝ ∞ cutoff := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun t => (hasDerivAt_cutoff t).differentiableAt, ?_⟩
  have : deriv cutoff = Real.smoothTransition := funext fun t => (hasDerivAt_cutoff t).deriv
  rw [this]
  exact Real.smoothTransition.contDiff (n := ⊤)

theorem cutoff_of_nonpos {t : ℝ} (ht : t ≤ 0) : cutoff t = 0 := by
  have : ∫ u in (0 : ℝ)..t, Real.smoothTransition u = ∫ _ in (0 : ℝ)..t, (0 : ℝ) :=
    intervalIntegral.integral_congr fun u hu => by
      rw [Set.uIcc_of_ge ht] at hu
      exact Real.smoothTransition.zero_of_nonpos hu.2
  rw [cutoff, this, intervalIntegral.integral_zero]

theorem cutoff_of_one_le {t : ℝ} (ht : 1 ≤ t) : cutoff t = t - (1 - cutoff 1) := by
  have hc := Real.smoothTransition.continuous
  have h1 : ∫ u in (1 : ℝ)..t, Real.smoothTransition u = ∫ _ in (1 : ℝ)..t, (1 : ℝ) :=
    intervalIntegral.integral_congr fun u hu => by
      rw [Set.uIcc_of_le ht] at hu
      exact Real.smoothTransition.one_of_one_le hu.1
  have h2 := intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable (μ := volume) 0 1)
    (hc.intervalIntegrable (μ := volume) 1 t)
  rw [h1, intervalIntegral.integral_const, smul_eq_mul, mul_one] at h2
  unfold cutoff
  linarith

theorem levi_add_const {ι : Type*} [Fintype ι] (f : (ι → ℂ) → ℝ) (c : ℝ) (z w : ι → ℂ) :
    levi (fun y => f y + c) z w = levi f z w := by
  have : fderiv ℝ (fun y => f y + c) = fderiv ℝ f := funext fun _ => fderiv_add_const c
  simp only [levi, this]

theorem levi_comp_real {ι : Type*} [Fintype ι] {ρ ρ' : ℝ → ℝ} {ρ'' : ℝ} {t : (ι → ℂ) → ℝ}
    {z : ι → ℂ} (hρ : ∀ u, HasDerivAt ρ (ρ' u) u) (hρ' : HasDerivAt ρ' ρ'' (t z))
    (ht : ContDiffAt ℝ 2 t z) (w : ι → ℂ) :
    levi (ρ ∘ t) z w = ρ' (t z) * levi t z w +
      ρ'' * ((fderiv ℝ t z w) ^ 2 + (fderiv ℝ t z (Complex.I • w)) ^ 2) / 4 := by
  have h1 : ∀ᶠ y in 𝓝 z, HasFDerivAt (ρ ∘ t) (ρ' (t y) • fderiv ℝ t y) y := by
    filter_upwards [ht.eventually (by simp)] with y hy
    exact (hρ (t y)).comp_hasFDerivAt y (hy.differentiableAt (by norm_num)).hasFDerivAt
  have h1' : fderiv ℝ (ρ ∘ t) =ᶠ[𝓝 z] fun y => ρ' (t y) • fderiv ℝ t y :=
    h1.mono fun y hy => hy.fderiv
  have ht' : HasFDerivAt (fderiv ℝ t) (fderiv ℝ (fderiv ℝ t) z) z :=
    ((ht.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have h2 : HasFDerivAt (fun y => ρ' (t y) • fderiv ℝ t y)
      (ρ' (t z) • fderiv ℝ (fderiv ℝ t) z + (ρ'' • fderiv ℝ t z).smulRight (fderiv ℝ t z)) z :=
    (hρ'.comp_hasFDerivAt z (ht.differentiableAt (by norm_num)).hasFDerivAt).smul ht'
  have h3 : fderiv ℝ (fderiv ℝ (ρ ∘ t)) z =
      ρ' (t z) • fderiv ℝ (fderiv ℝ t) z + (ρ'' • fderiv ℝ t z).smulRight (fderiv ℝ t z) := by
    rw [h1'.fderiv_eq]
    exact h2.fderiv
  simp only [levi, h3, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  ring

theorem hessC_add_const {D : ℕ} (f : (Fin D → ℂ) → ℝ) (c : ℝ) (z : Fin D → ℂ) :
    hessC (fun y => f y + c) z = hessC f z := by
  have : fderiv ℝ (fun y => f y + c) = fderiv ℝ f := funext fun _ => fderiv_add_const c
  unfold hessC
  rw [this]

theorem isPsh_shift {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (P : LocPot X) (a b : X → ℝ) (k : ℝ) (hP : IsPotential A P) (ha : A.Smooth a)
    (hb : A.Smooth b) (hPa : IsPsh A (P + LocPot.ofFun a)) (hPb : IsPsh A (P + LocPot.ofFun b)) :
    IsPsh A ((P + LocPot.ofFun a) + LocPot.ofFun (fun x => cutoff (b x - a x + k))) := by
  intro x j y hy w
  have hyP : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x := ⟨hy.1, hy.2.1.1⟩
  have hT : (A.chart j).target ∈ 𝓝 y := (A.chart j).open_target.mem_nhds hy.1
  have sm : ∀ f : X → ℝ, A.Smooth f → ContDiffAt ℝ 2 (f ∘ (A.chart j).symm) y := fun f hf => by
    have := hf j
    rw [Set.preimage_univ, Set.inter_univ] at this
    exact (this.contDiffAt hT).of_le (WithTop.coe_le_coe.2 le_top)
  have hφ := potSmoothAt A P hP x j hyP
  have hα := sm a ha
  have hβ := sm b hb
  have ht : ContDiffAt ℝ 2 (fun z => b ((A.chart j).symm z) - a ((A.chart j).symm z) + k) y :=
    (hβ.sub hα).add contDiffAt_const
  have hsT : HasDerivAt Real.smoothTransition
      (deriv Real.smoothTransition (b ((A.chart j).symm y) - a ((A.chart j).symm y) + k))
      (b ((A.chart j).symm y) - a ((A.chart j).symm y) + k) :=
    ((Real.smoothTransition.contDiffAt (n := 1)).differentiableAt (by simp)).hasDerivAt
  have hc : ContDiffAt ℝ 2 (cutoff ∘ fun z => b ((A.chart j).symm z) - a ((A.chart j).symm z) + k) y :=
    ((contDiff_cutoff.of_le (WithTop.coe_le_coe.2 le_top)).contDiffAt).comp y ht
  have hL1 : ∀ f : X → ℝ, A.Smooth f →
      levi (fun z => P.φ x ((A.chart j).symm z) + f ((A.chart j).symm z)) y w =
        levi (P.φ x ∘ (A.chart j).symm) y w + levi (f ∘ (A.chart j).symm) y w := fun f hf => by
    have := levi_add_smul (f := P.φ x ∘ (A.chart j).symm) (g := f ∘ (A.chart j).symm) 1 hφ
      (sm f hf) w
    simpa using this
  have hPa0 : 0 ≤ levi (P.φ x ∘ (A.chart j).symm) y w + levi (a ∘ (A.chart j).symm) y w := by
    rw [← hL1 a ha]
    exact hPa x j y ⟨hy.1, hy.2.1⟩ w
  have hPb0 : 0 ≤ levi (P.φ x ∘ (A.chart j).symm) y w + levi (b ∘ (A.chart j).symm) y w := by
    rw [← hL1 b hb]
    exact hPb x j y ⟨hy.1, hy.2.1⟩ w
  have hLt : levi (fun z => b ((A.chart j).symm z) - a ((A.chart j).symm z) + k) y w =
      levi (b ∘ (A.chart j).symm) y w - levi (a ∘ (A.chart j).symm) y w := by
    rw [levi_add_const (fun z => b ((A.chart j).symm z) - a ((A.chart j).symm z)) k]
    have := levi_add_smul (f := b ∘ (A.chart j).symm) (g := a ∘ (A.chart j).symm) (-1) hβ hα w
    have e : (fun z => b ((A.chart j).symm z) - a ((A.chart j).symm z)) =
        fun z => (b ∘ (A.chart j).symm) z + -1 * (a ∘ (A.chart j).symm) z := by
      funext z; simp only [Function.comp_apply]; ring
    rw [e, this]
    ring
  have hF : ((P + LocPot.ofFun a) + LocPot.ofFun (fun x => cutoff (b x - a x + k))).φ x ∘
      (A.chart j).symm = fun z => (P.φ x ((A.chart j).symm z) + a ((A.chart j).symm z)) +
        1 * (cutoff ∘ fun z => b ((A.chart j).symm z) - a ((A.chart j).symm z) + k) z := by
    funext z
    simp only [Function.comp_apply, one_mul]
    rfl
  rw [hF, levi_add_smul (f := fun z => P.φ x ((A.chart j).symm z) + a ((A.chart j).symm z)) 1
    (hφ.add hα) hc w, hL1 a ha, levi_comp_real hasDerivAt_cutoff hsT ht w, hLt]
  have hs0 := Real.smoothTransition.nonneg (b ((A.chart j).symm y) - a ((A.chart j).symm y) + k)
  have hs1 := Real.smoothTransition.le_one (b ((A.chart j).symm y) - a ((A.chart j).symm y) + k)
  have hd : 0 ≤ deriv Real.smoothTransition (b ((A.chart j).symm y) - a ((A.chart j).symm y) + k) :=
    Real.smoothTransition.monotone.deriv_nonneg
  have hq : 0 ≤ (fderiv ℝ (fun z => b ((A.chart j).symm z) - a ((A.chart j).symm z) + k) y w) ^ 2 +
      (fderiv ℝ (fun z => b ((A.chart j).symm z) - a ((A.chart j).symm z) + k) y
        (Complex.I • w)) ^ 2 := by positivity
  nlinarith [mul_nonneg (sub_nonneg.2 hs1) hPa0, mul_nonneg hs0 hPb0, mul_nonneg hd hq]

theorem maMeasure_congr_open {e : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] (A : FinHolAtlas e X) (Φ Ψ : Fin e → LocPot X) {S : Set X} (hS : IsOpen S)
    (h : ∀ j, ∀ y ∈ (A.chart j).target, (A.chart j).symm y ∈ S →
      locDens A Φ j y = locDens A Ψ j y) :
    maMeasure A Φ S = maMeasure A Ψ S := by
  by_cases hne : Nonempty (ChartPartition A)
  · rw [maMeasure_eq_sum A Φ hne, maMeasure_eq_sum A Ψ hne]
    simp only [Measure.coe_finsetSum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold chartMeasure
    have hTm := (A.chart j).open_target.measurableSet
    have hsm : AEMeasurable (A.chart j).symm (volume.restrict (A.chart j).target) :=
      (A.chart j).continuousOn_symm.aemeasurable hTm
    rw [Measure.map_apply_of_aemeasurable (hsm.mono_ac (withDensity_absolutelyContinuous _ _))
        hS.measurableSet,
      Measure.map_apply_of_aemeasurable (hsm.mono_ac (withDensity_absolutelyContinuous _ _))
        hS.measurableSet, withDensity_apply', withDensity_apply', Measure.restrict_restrict' hTm]
    have hV : IsOpen ((A.chart j).symm ⁻¹' S ∩ (A.chart j).target) := by
      rw [Set.inter_comm]
      exact (A.chart j).isOpen_inter_preimage_symm hS
    refine setLIntegral_congr_fun hV.measurableSet fun y hy => ?_
    simp only [h j y hy.2 hy.1]
  · unfold maMeasure
    rw [dif_neg hne, dif_neg hne]

theorem maMeasure_compact_eq {e : ℕ} {X : Type} [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] (A : FinHolAtlas e X) (Φ : Fin e → LocPot X)
    (hne : Nonempty (ChartPartition A)) (hΦ : ∀ i, IsPotential A (Φ i))
    (hPsh : ∀ i, IsPsh A (Φ i)) {K : Set X} (hK : IsCompact K) :
    maMeasure A Φ K = ENNReal.ofReal (mInt A Φ (K.indicator 1)) := by
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hg : Measurable (K.indicator (1 : X → ℝ)) := measurable_const.indicator hKm
  have hw0 : ∀ j, ∀ y ∈ (A.chart j).target,
      0 ≤ hne.some.χ j ((A.chart j).symm y) * locDens A Φ j y := fun j y hy =>
    mul_nonneg (hne.some.nonneg j _) (locDens_nonneg_of_psh A Φ hΦ hPsh j hy)
  have hj : ∀ j, chartMeasure A hne.some Φ j K =
      ENNReal.ofReal (∫ y in (A.chart j).target, K.indicator 1 ((A.chart j).symm y) *
        (hne.some.χ j ((A.chart j).symm y) * locDens A Φ j y)) := by
    intro j
    have hw : ContinuousOn (fun y => hne.some.χ j ((A.chart j).symm y) * locDens A Φ j y)
        (A.chart j).target :=
      (chi_comp_continuousOn hne.some j).mul (locDensCont A Φ hΦ j)
    have key := map_withDensity_integrable_integral (A.chart j).open_target
      (A.chart j).continuousOn_symm hw (hw0 j) hg
    have hZ : IsCompact (K ∩ tsupport (hne.some.χ j)) := hK.inter_right (isClosed_tsupport _)
    have hZs : K ∩ tsupport (hne.some.χ j) ⊆ (A.chart j).source := fun x hx =>
      hne.some.tsupport_subset j hx.2
    have hC : IsCompact ((A.chart j) '' (K ∩ tsupport (hne.some.χ j))) :=
      hZ.image_of_continuousOn ((A.chart j).continuousOn.mono hZs)
    have hCT : (A.chart j) '' (K ∩ tsupport (hne.some.χ j)) ⊆ (A.chart j).target :=
      Set.image_subset_iff.mpr fun x hx => (A.chart j).map_source (hZs hx)
    have hCm : MeasurableSet ((A.chart j) '' (K ∩ tsupport (hne.some.χ j))) :=
      hC.isClosed.measurableSet
    have hint : IntegrableOn (fun y => K.indicator 1 ((A.chart j).symm y) *
        (hne.some.χ j ((A.chart j).symm y) * locDens A Φ j y)) (A.chart j).target := by
      refine integrableOn_target_of_closed (A.chart j) (Z := K ∩ tsupport (hne.some.χ j)) ?_ ?_
      · intro y _ hyZ
        by_cases hyK : (A.chart j).symm y ∈ K
        · have : (A.chart j).symm y ∉ tsupport (hne.some.χ j) := fun h => hyZ ⟨hyK, h⟩
          simp [image_eq_zero_of_notMem_tsupport this]
        · simp [hyK]
      · have hwi : IntegrableOn (fun y => hne.some.χ j ((A.chart j).symm y) * locDens A Φ j y)
            ((A.chart j) '' (K ∩ tsupport (hne.some.χ j))) :=
          (hw.mono hCT).integrableOn_compact hC
        have hs1 : AEMeasurable (A.chart j).symm
            (volume.restrict ((A.chart j) '' (K ∩ tsupport (hne.some.χ j)))) :=
          ((A.chart j).continuousOn_symm.mono hCT).aemeasurable hCm
        refine Integrable.mono' hwi
          ((hg.comp_aemeasurable hs1).mul ((hw.mono hCT).aemeasurable hCm)).aestronglyMeasurable
          (ae_restrict_of_forall_mem hCm fun y hy => ?_)
        have hy0 := hw0 j y (hCT hy)
        have h1 : |K.indicator (1 : X → ℝ) ((A.chart j).symm y)| ≤ 1 := by
          by_cases h : (A.chart j).symm y ∈ K <;> simp [h]
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hy0]
        exact mul_le_of_le_one_left hy0 h1
    have hi : Integrable (K.indicator (1 : X → ℝ)) (chartMeasure A hne.some Φ j) := key.1.mpr hint
    have e2 : ∫ x, K.indicator (1 : X → ℝ) x ∂chartMeasure A hne.some Φ j =
        ∫ y in (A.chart j).target, K.indicator 1 ((A.chart j).symm y) *
          (hne.some.χ j ((A.chart j).symm y) * locDens A Φ j y) := key.2
    rw [← e2, ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) x)]
    have : (fun x => ENNReal.ofReal (K.indicator (1 : X → ℝ) x)) = K.indicator 1 := by
      funext x
      by_cases h : x ∈ K <;> simp [h]
    rw [this, lintegral_indicator_one hKm]
  rw [maMeasure_eq_sum A Φ hne]
  simp only [Measure.coe_finsetSum, Finset.sum_apply, hj]
  have hsum := ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
    (f := fun j => ∫ y in (A.chart j).target, K.indicator (1 : X → ℝ) ((A.chart j).symm y) *
      (hne.some.χ j ((A.chart j).symm y) * locDens A Φ j y))
    fun j _ => setIntegral_nonneg (A.chart j).open_target.measurableSet fun y hy =>
      mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _) (hw0 j y hy)
  rw [← hsum]
  congr 1
  rw [mInt_eq_integralWith A Φ hne]
  unfold integralWith
  refine Finset.sum_congr rfl fun j _ => integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  ring

theorem proof (h : MongeAmpereCompactChange.Statement) : MongeAmpereComparison.Statement := by
  intro e X _ _ _ _ A P a b hyp
  obtain ⟨hP, ha, hb, hPa, hPb, hK⟩ := hyp
  by_cases hne : Nonempty (ChartPartition A)
  swap
  · unfold maMeasure
    rw [dif_neg hne, dif_neg hne]
  have hac := projLine_continuous_of_smooth A ha
  have hbc := projLine_continuous_of_smooth A hb
  let v : ℕ → X → ℝ := fun k x => cutoff (b x - a x + (k : ℝ))
  let S : ℕ → Set X := fun k => {x | -(k : ℝ) + 1 < b x - a x}
  let K : ℕ → Set X := fun k => {x | -(k : ℝ) ≤ b x - a x}
  have hSo : ∀ k, IsOpen (S k) := fun k => isOpen_lt continuous_const (hbc.sub hac)
  have hSK : ∀ k, S k ⊆ K k := fun k x hx => by
    simp only [S, K, Set.mem_ofPred_eq] at hx ⊢
    linarith
  have hSmono : Monotone S := fun k l hkl x hx => by
    simp only [S, Set.mem_ofPred_eq] at hx ⊢
    have : (k : ℝ) ≤ l := by exact_mod_cast hkl
    linarith
  have hSU : (⋃ k, S k) = Set.univ := by
    refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ?_
    obtain ⟨k, hk⟩ := exists_nat_gt (1 - (b x - a x))
    exact ⟨k, by simp only [S, Set.mem_ofPred_eq]; linarith⟩
  have hPa' : IsPotential A (P + LocPot.ofFun a) := isPotentialAdd A _ _ hP (isPotential_ofFun A a ha)
  have hv : ∀ k, A.Smooth (v k) := fun k j =>
    contDiff_cutoff.comp_contDiffOn (((hb j).sub (ha j)).add contDiffOn_const)
  have hPk : ∀ k, IsPotential A ((P + LocPot.ofFun a) + LocPot.ofFun (v k)) := fun k =>
    isPotentialAdd A _ _ hPa' (isPotential_ofFun A _ (hv k))
  have hPsk : ∀ k : ℕ, IsPsh A ((P + LocPot.ofFun a) + LocPot.ofFun (v k)) := fun k =>
    isPsh_shift A P a b k hP ha hb hPa hPb
  have step : ∀ k : ℕ, maMeasure A (fun _ => P + LocPot.ofFun b) (S k) ≤
      maMeasure A (fun _ => P + LocPot.ofFun a) Set.univ := by
    intro k
    have hKc : IsCompact (K k) := hK k
    have hsupp : Function.support (v k) ⊆ K k := by
      intro x hx
      simp only [Function.mem_support] at hx
      simp only [K, Set.mem_ofPred_eq]
      by_contra hlt
      exact hx (cutoff_of_nonpos (by linarith [not_le.mp hlt]))
    have htsupp : tsupport (v k) ⊆ K k := closure_minimal hsupp hKc.isClosed
    have hcs : HasCompactSupport (v k) := hKc.of_isClosed_subset (isClosed_tsupport _) htsupp
    have h2 := h A (P + LocPot.ofFun a) (v k) (K k) ⟨hPa', hv k, hcs, hKc, htsupp⟩
    have hloc : maMeasure A (fun _ => P + LocPot.ofFun b) (S k) =
        maMeasure A (fun _ => (P + LocPot.ofFun a) + LocPot.ofFun (v k)) (S k) := by
      apply maMeasure_congr_open A _ _ (hSo k)
      intro j y hy hyS
      unfold locDens
      apply maDens_congr_hessC
      intro i
      have hV : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' S k) :=
        (A.chart j).isOpen_inter_preimage_symm (hSo k)
      have hev : (fun y' => ((P + LocPot.ofFun a) + LocPot.ofFun (v k)).φ ((A.chart j).symm y)
            ((A.chart j).symm y')) =ᶠ[𝓝 y]
          fun y' => (P + LocPot.ofFun b).φ ((A.chart j).symm y) ((A.chart j).symm y') +
            ((k : ℝ) - (1 - cutoff 1)) := by
        filter_upwards [hV.mem_nhds ⟨hy, hyS⟩] with y' hy'
        have h1 : 1 ≤ b ((A.chart j).symm y') - a ((A.chart j).symm y') + k := by
          have := hy'.2
          simp only [S, Set.mem_preimage, Set.mem_ofPred_eq] at this
          linarith
        show (P.φ _ _ + a _) + cutoff (b _ - a _ + (k : ℝ)) = (P.φ _ _ + b _) + ((k : ℝ) - (1 - cutoff 1))
        rw [cutoff_of_one_le h1]
        ring
      show hessC (fun y' => (P + LocPot.ofFun b).φ ((A.chart j).symm y) ((A.chart j).symm y')) y =
        hessC (fun y' => ((P + LocPot.ofFun a) + LocPot.ofFun (v k)).φ ((A.chart j).symm y)
          ((A.chart j).symm y')) y
      rw [hessCGerm _ _ _ hev, hessC_add_const]
    calc maMeasure A (fun _ => P + LocPot.ofFun b) (S k)
        = maMeasure A (fun _ => (P + LocPot.ofFun a) + LocPot.ofFun (v k)) (S k) := hloc
      _ ≤ maMeasure A (fun _ => (P + LocPot.ofFun a) + LocPot.ofFun (v k)) (K k) :=
          measure_mono (hSK k)
      _ = ENNReal.ofReal (mInt A (fun _ => (P + LocPot.ofFun a) + LocPot.ofFun (v k))
            ((K k).indicator 1)) :=
          maMeasure_compact_eq A _ hne (fun _ => hPk k) (fun _ => hPsk k) hKc
      _ = ENNReal.ofReal (mInt A (fun _ => P + LocPot.ofFun a) ((K k).indicator 1)) := by rw [h2]
      _ = maMeasure A (fun _ => P + LocPot.ofFun a) (K k) :=
          (maMeasure_compact_eq A _ hne (fun _ => hPa') (fun _ => hPa) hKc).symm
      _ ≤ maMeasure A (fun _ => P + LocPot.ofFun a) Set.univ := measure_mono (Set.subset_univ _)
  calc maMeasure A (fun _ => P + LocPot.ofFun b) Set.univ
      = ⨆ k, maMeasure A (fun _ => P + LocPot.ofFun b) (S k) := by
        rw [← hSU]
        exact hSmono.measure_iUnion
    _ ≤ maMeasure A (fun _ => P + LocPot.ofFun a) Set.univ := iSup_le step

end MongeAmpereComparison

end

end GroundTheory.Heights₂.Heights.FourB
