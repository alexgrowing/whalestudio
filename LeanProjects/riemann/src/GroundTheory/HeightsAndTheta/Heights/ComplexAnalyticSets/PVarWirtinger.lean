import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StVarWirtinger
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StDiscriminantSheetCover
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetComass
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetAreaCompare
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetImageAreaSet
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNullSmaller
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBadSetSmaller
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets ReciprocityTheory.AnForm
open scoped ENNReal ComplexOrder

noncomputable section

namespace VarWirtinger

theorem maDens_euclPot_comp {n D : ℕ} (s : (Fin D → ℂ) → Fin n → ℂ) (y : Fin D → ℂ)
    (hs : AnalyticAt ℂ s y) :
    maDens (fun _ : Fin D => (euclPot : (Fin n → ℂ) → ℝ) ∘ s) y =
      (D.factorial : ℝ) * (2 / Real.pi) ^ D * sheetJac s y := by
  have hφ : ContDiffAt ℝ 2 (euclPot : (Fin n → ℂ) → ℝ) (s y) :=
    (contDiff_euclPot n).contDiffAt.of_le (WithTop.coe_le_coe.2 le_top)
  set M := ReciprocityTheory.AnForm.A.jacC s y with hM
  have hH : hessC ((euclPot : (Fin n → ℂ) → ℝ) ∘ s) y = Mᵀ * M.map (starRingEnd ℂ) := by
    rw [ReciprocityTheory.AnForm.A.hessC_comp _ s y hs hφ, TubeFormComparison.hessC_euclPot, Matrix.mul_one]
  have hdet : (Mᵀ * M.map (starRingEnd ℂ)).det = starRingEnd ℂ (Mᴴ * M).det := by
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp [Matrix.mul_apply, mul_comm]
  have hnn : 0 ≤ (Mᴴ * M).det := (Matrix.posSemidef_conjTranspose_mul_self M).det_nonneg
  have hre : (starRingEnd ℂ (Mᴴ * M).det).re = ‖(Mᴴ * M).det‖ := by
    obtain ⟨h1, h2⟩ := Complex.nonneg_iff.1 hnn
    have e : (Mᴴ * M).det = (((Mᴴ * M).det.re : ℝ) : ℂ) := Complex.ext rfl (by simp [← h2])
    rw [e, Complex.conj_ofReal, Complex.ofReal_re, Complex.norm_real, Real.norm_of_nonneg h1]
  rw [SheetComassAlt.sheetJac_eq_norm_det s y hs.differentiableAt, ← hre, ← hdet, ← hH]
  unfold maDens
  rw [ReciprocityTheory.AnForm.A.mdisc_const]

end VarWirtinger

open VarWirtinger in

theorem VarWirtinger.proof (hDSC : DiscriminantSheetCover.Statement) (hMF : MassFinite.Statement) :
    VarWirtinger.Statement := by
  classical
  intro d
  obtain ⟨cH, hcH⟩ := SheetAreaCompare.exists_lintegral_volume_eq (d + 1)
  set κ : ℝ := ((d + 1).factorial : ℝ) * (2 / Real.pi) ^ (d + 1) with hκ
  have hκ0 : 0 < κ := by positivity
  have hcH0 : cH ≠ 0 := by
    intro h0
    have h1 := hcH (fun _ => 1)
    rw [h0, ENNReal.coe_zero, zero_mul, lintegral_const, one_mul, Measure.measure_univ_eq_zero] at h1
    exact (NeZero.ne (volume : Measure (Fin (d + 1) → ℂ))) h1
  have hcHpos : (0 : ℝ) < cH := by exact_mod_cast pos_iff_ne_zero.2 hcH0
  refine ⟨1 / (κ * cH), by positivity, ?_⟩
  intro n J A hJ hdim hA B hBm hBb
  obtain ⟨P, U, Dk, N, s, hP, hUD, hdisj, hcomp, hvol, hfib⟩ := hDSC n (d + 1) J A hJ hdim hA
  set g : (Fin n → ℂ) → ℝ := ((fun x => WithLp.toLp 2 x) ⁻¹' B).indicator fun _ => 1 with hg
  set f := chartDens J A g (fun _ => euclPot) with hf
  have hgm : Measurable g :=
    measurable_const.indicator (hBm.preimage (PiLp.continuous_toLp 2 _).measurable)
  have hfm : Measurable f := (SheetSumMeasurable.proof n (d + 1) J A g _ hJ hdim hA hgm
    (fun _ => smoothNear_of_contDiff (contDiff_euclPot n))).1

  have hterm : ∀ x y, x ∈ fibre J A y → ∀ h : ∃ s, IsSheetAt J A x s,
      maDens (fun _ : Fin (d + 1) => (euclPot : (Fin n → ℂ) → ℝ) ∘ h.choose) y = κ * sheetJac h.choose y := by
    intro x y hx h
    obtain ⟨V, hV, hyV, hsd, -, -, -⟩ := h.choose_spec
    rw [hx.2] at hyV
    exact maDens_euclPot_comp _ _ (IndefiniteRowSideFullHecke.ComplexSets.analyticOnNhd_of_differentiableOn hV hsd _ hyV)
  have hf0 : ∀ y, 0 ≤ f y := by
    intro y
    simp only [hf, chartDens, sheetSum]
    refine finsum_nonneg fun x => finsum_nonneg fun hx => ?_
    split_ifs with h
    · rw [hterm x y hx h]
      exact mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
        (mul_nonneg hκ0.le (sheetJac_nonneg _ _))
    · exact le_rfl

  have hsec : ∀ k j, ∀ y ∈ U k, A *ᵥ s k j y = y ∧ s k j y ∈ zeroSet J := by
    intro k j y hy
    have hx : s k j y ∈ fibre J A y := (hfib k y hy).1 ▸ ⟨j, rfl⟩
    exact ⟨hx.2, hx.1⟩

  have hDk : ∀ k, ∀ y ∈ Dk k, f y = ∑ j : Fin (N k), g (s k j y) * (κ * sheetJac (s k j) y) := by
    intro k y hy
    obtain ⟨hfibeq, hinj, hsh⟩ := hfib k y ((hUD k).2.2.1 hy)
    simp only [hf, chartDens, sheetSum]
    rw [hfibeq, finsum_mem_range hinj, finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h : ∃ s', IsSheetAt J A (s k j y) s' := ⟨_, hsh j⟩
    rw [dif_pos h]
    have hxf : s k j y ∈ fibre J A y := hfibeq ▸ ⟨j, rfl⟩
    rw [hterm _ _ hxf h]
    have heq := SheetSumMeasurable.sheet_eventuallyEq (hsh j) h.choose_spec
    rw [hxf.2] at heq
    rw [sheetJac, sheetJac, heq.fderiv_eq]

  set E : ∀ k, Fin (N k) → Set (Fin (d + 1) → ℂ) := fun k j => Dk k ∩ {y | WithLp.toLp 2 (s k j y) ∈ B}
    with hE
  set E' : ∀ k, Fin (N k) → Set (EuclideanSpace ℂ (Fin (d + 1))) := fun k j => WithLp.ofLp ⁻¹' E k j with hE'
  set T : ∀ k, Fin (N k) → EuclideanSpace ℂ (Fin (d + 1)) → EuclideanSpace ℂ (Fin n) :=
    fun k j y => WithLp.toLp 2 (s k j (WithLp.ofLp y)) with hT
  set S : ∀ k, Fin (N k) → Set (EuclideanSpace ℂ (Fin n)) := fun k j => T k j '' E' k j with hS
  have hEm : ∀ k j, MeasurableSet (E k j) := by
    intro k j
    have hpm : Measurable ((U k).piecewise (s k j) fun _ => 0) :=
      ((hUD k).2.2.2 j).continuousOn.measurable_piecewise continuousOn_const (hUD k).1.measurableSet
    have e : E k j = Dk k ∩ ((U k).piecewise (s k j) fun _ => 0) ⁻¹' ((fun x => WithLp.toLp 2 x) ⁻¹' B) := by
      ext y
      simp only [hE, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage]
      constructor
      · rintro ⟨hy, hB⟩
        exact ⟨hy, by rw [Set.piecewise_eq_of_mem _ _ _ ((hUD k).2.2.1 hy)]; exact hB⟩
      · rintro ⟨hy, hB⟩
        exact ⟨hy, by rw [Set.piecewise_eq_of_mem _ _ _ ((hUD k).2.2.1 hy)] at hB; exact hB⟩
    rw [e]
    exact (hUD k).2.1.inter (hpm (hBm.preimage (PiLp.continuous_toLp 2 _).measurable))
  have hE'm : ∀ k j, MeasurableSet (E' k j) := fun k j =>
    (hEm k j).preimage (PiLp.continuous_ofLp 2 _).measurable
  have hE'U : ∀ k j, ∀ y ∈ E' k j, WithLp.ofLp y ∈ U k := fun k j y hy => (hUD k).2.2.1 hy.1
  have hSm : ∀ k j, MeasurableSet (S k j) := by
    intro k j
    refine (hE'm k j).image_of_continuousOn_injOn ?_ ?_
    · exact (PiLp.continuous_toLp 2 _).comp_continuousOn
        (((hUD k).2.2.2 j).continuousOn.comp (PiLp.continuous_ofLp 2 _).continuousOn (hE'U k j))
    · intro y₁ h₁ y₂ h₂ h12
      have h' : s k j (WithLp.ofLp y₁) = s k j (WithLp.ofLp y₂) := WithLp.toLp_injective 2 h12
      have e₁ := (hsec k j _ (hE'U k j y₁ h₁)).1
      have e₂ := (hsec k j _ (hE'U k j y₂ h₂)).1
      exact WithLp.ofLp_injective 2 (by rw [← e₁, ← e₂, h'])

  have hArea : ∀ k j, μH[((2 * (d + 1) : ℕ) : ℝ)] (S k j) =
      ∫⁻ y in E' k j, ENNReal.ofReal (sheetJac (s k j) (WithLp.ofLp y)) ∂(μH[((2 * (d + 1) : ℕ) : ℝ)]) :=
    fun k j => SheetImageAreaSet.proof n (d + 1) A (U k) (s k j) (hUD k).1 ((hUD k).2.2.2 j)
      (fun y hy => (hsec k j y hy).1) (E' k j) (hE'm k j) (hE'U k j)

  have hint : ∫⁻ y, ENNReal.ofReal (f y) =
      ENNReal.ofReal κ * cH * ∑' k, ∑ j : Fin (N k), μH[((2 * (d + 1) : ℕ) : ℝ)] (S k j) := by
    have hae : ∀ᵐ y ∂(volume : Measure (Fin (d + 1) → ℂ)), y ∈ ⋃ k, Dk k := by
      rw [ae_iff]
      simpa [Set.compl_def] using hvol
    rw [← Measure.restrict_eq_self_of_ae_mem hae, lintegral_iUnion (fun k => (hUD k).2.1) hdisj,
      ← ENNReal.tsum_mul_left]
    refine tsum_congr fun k => ?_
    have h1 : ∀ y ∈ Dk k, ENNReal.ofReal (f y) =
        ∑ j : Fin (N k), (E k j).indicator (fun y => ENNReal.ofReal κ * ENNReal.ofReal (sheetJac (s k j) y)) y := by
      intro y hy
      rw [hDk k y hy, ENNReal.ofReal_sum_of_nonneg fun j _ => mul_nonneg
        (Set.indicator_nonneg (fun _ _ => zero_le_one) _) (mul_nonneg hκ0.le (sheetJac_nonneg _ _))]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hB : WithLp.toLp 2 (s k j y) ∈ B
      · rw [Set.indicator_of_mem (show y ∈ E k j from ⟨hy, hB⟩),
          Set.indicator_of_mem (show s k j y ∈ (fun x => WithLp.toLp 2 x) ⁻¹' B from hB), one_mul,
          ENNReal.ofReal_mul hκ0.le]
      · rw [Set.indicator_of_notMem (show y ∉ E k j from fun h => hB h.2),
          Set.indicator_of_notMem (show s k j y ∉ (fun x => WithLp.toLp 2 x) ⁻¹' B from hB), zero_mul,
          ENNReal.ofReal_zero]
    rw [setLIntegral_congr_fun (hUD k).2.1 h1, lintegral_finset_sum _ (fun j _ =>
      (((SheetAreaCompare.measurable_sheetJac (s k j)).ennreal_ofReal.const_mul (ENNReal.ofReal κ)).indicator
        (hEm k j))), Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hsub : E k j ⊆ Dk k := Set.inter_subset_left
    rw [lintegral_indicator (hEm k j), Measure.restrict_restrict (hEm k j), Set.inter_eq_left.2 hsub,
      lintegral_const_mul _ (SheetAreaCompare.measurable_sheetJac _).ennreal_ofReal, mul_assoc, hArea,
      ← lintegral_indicator (hEm k j), hcH, ← lintegral_indicator (hE'm k j)]
    rfl

  have hnull : μH[((2 * (d + 1) : ℕ) : ℝ)]
      (zeroSetEuc J ∩ {z : EuclideanSpace ℂ (Fin n) | A *ᵥ WithLp.ofLp z ∉ ⋃ k, Dk k}) = 0 := by
    obtain ⟨hZ, hdimQ⟩ := BadSetSmaller.proof n (d + 1) J A hJ hdim hA P hP
    set I := J ⊔ Ideal.span {pullback A P}
    have hsub : zeroSetEuc J ∩ {z : EuclideanSpace ℂ (Fin n) | A *ᵥ WithLp.ofLp z ∉ ⋃ k, Dk k} ⊆
        ⋃ Q ∈ I.minimalPrimes, zeroSetEuc Q := by
      rintro z ⟨hzJ, hzD⟩
      have hzI : WithLp.ofLp z ∈ zeroSet I := by
        rw [hZ]
        exact ⟨hzJ, hcomp hzD⟩
      have hle : I ≤ RingHom.ker (MvPolynomial.eval (WithLp.ofLp z)) := fun q hq => hzI q hq
      haveI : (RingHom.ker (MvPolynomial.eval (WithLp.ofLp z))).IsPrime :=
        RingHom.ker_isPrime _
      obtain ⟨Q, hQ, hQle⟩ := Ideal.exists_minimalPrimes_le hle
      exact Set.mem_biUnion hQ fun q hq => hQle hq
    refine measure_mono_null hsub ((measure_biUnion_null_iff
      (Ideal.finite_minimalPrimes_of_isNoetherianRing _ I).countable).2 fun Q hQ => ?_)
    exact NullSmaller.proof n (d + 1) Q (hdimQ Q hQ)

  have hunion : zeroSetEuc J ∩ B ∩ {z : EuclideanSpace ℂ (Fin n) | A *ᵥ WithLp.ofLp z ∈ ⋃ k, Dk k} =
      ⋃ k, ⋃ j, S k j := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨⟨hzJ, hzB⟩, k, hk⟩
      obtain ⟨hfibeq, -, -⟩ := hfib k _ ((hUD k).2.2.1 hk)
      have hzf : WithLp.ofLp z ∈ fibre J A (A *ᵥ WithLp.ofLp z) := ⟨hzJ, rfl⟩
      rw [hfibeq] at hzf
      obtain ⟨j, hj⟩ := hzf
      replace hj : s k j (A *ᵥ WithLp.ofLp z) = WithLp.ofLp z := hj
      refine ⟨k, j, WithLp.toLp 2 (A *ᵥ WithLp.ofLp z), ⟨hk, ?_⟩, ?_⟩
      · show WithLp.toLp 2 (s k j (A *ᵥ WithLp.ofLp z)) ∈ B
        rw [hj]
        exact hzB
      · show WithLp.toLp 2 (s k j (A *ᵥ WithLp.ofLp z)) = z
        rw [hj]
    · rintro ⟨k, j, y, ⟨hyD, hyB⟩, rfl⟩
      obtain ⟨e₁, e₂⟩ := hsec k j _ ((hUD k).2.2.1 hyD)
      refine ⟨⟨fun q hq => e₂ q hq, hyB⟩, k, ?_⟩
      show A *ᵥ s k j (WithLp.ofLp y) ∈ Dk k
      rw [e₁]
      exact hyD
  have hdisjS : ∀ k, Pairwise (Function.onFun Disjoint (S k)) := by
    intro k j j' hjj'
    rw [Function.onFun, Set.disjoint_left]
    rintro _ ⟨y, hy, rfl⟩ ⟨y', hy', hyy'⟩
    have h' : s k j' (WithLp.ofLp y') = s k j (WithLp.ofLp y) := WithLp.toLp_injective 2 hyy'
    have e : WithLp.ofLp y' = WithLp.ofLp y := by
      rw [← (hsec k j' _ (hE'U k j' y' hy')).1, ← (hsec k j _ (hE'U k j y hy)).1, h']
    rw [e] at h'
    exact hjj' ((hfib k _ (hE'U k j y hy)).2.1 h').symm
  have hdisjK : Pairwise (Function.onFun Disjoint fun k => ⋃ j, S k j) := by
    intro k k' hkk'
    rw [Function.onFun, Set.disjoint_left]
    intro z hz hz'
    have hA : ∀ k, z ∈ ⋃ j, S k j → A *ᵥ WithLp.ofLp z ∈ Dk k := by
      intro k hz
      obtain ⟨j, y, hy, rfl⟩ := Set.mem_iUnion.1 hz
      show A *ᵥ s k j (WithLp.ofLp y) ∈ Dk k
      rw [(hsec k j _ (hE'U k j y hy)).1]
      exact hy.1
    exact Set.disjoint_left.1 (hdisj hkk') (hA k hz) (hA k' hz')
  have hmeas : μH[((2 * (d + 1) : ℕ) : ℝ)] (zeroSetEuc J ∩ B) =
      ∑' k, ∑ j : Fin (N k), μH[((2 * (d + 1) : ℕ) : ℝ)] (S k j) := by
    have e : (zeroSetEuc J ∩ B) \ (zeroSetEuc J ∩ {z : EuclideanSpace ℂ (Fin n) | A *ᵥ WithLp.ofLp z ∉ ⋃ k, Dk k}) =
        zeroSetEuc J ∩ B ∩ {z : EuclideanSpace ℂ (Fin n) | A *ᵥ WithLp.ofLp z ∈ ⋃ k, Dk k} := by
      ext z
      simp only [Set.mem_diff, Set.mem_inter_iff, Set.mem_setOf_eq]
      tauto
    rw [← measure_diff_null hnull, e, hunion, measure_iUnion hdisjK
      (fun k => MeasurableSet.iUnion fun j => hSm k j)]
    refine tsum_congr fun k => ?_
    rw [measure_iUnion (hdisjS k) (hSm k), tsum_fintype]

  obtain ⟨R, hR⟩ := hBb.subset_ball (0 : EuclideanSpace ℂ (Fin n))
  have hfin : μH[((2 * (d + 1) : ℕ) : ℝ)] (zeroSetEuc J ∩ B) < ⊤ :=
    (measure_mono (Set.inter_subset_inter_right _ hR)).trans_lt (hMF n (d + 1) J hJ hdim R)
  have hlt : ∫⁻ y, ENNReal.ofReal (f y) < ⊤ := by
    rw [hint, ← hmeas]
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.coe_lt_top) hfin
  have hfi : Integrable f :=
    ⟨hfm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (ae_of_all _ hf0)).2 hlt⟩
  refine ⟨hfi, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hf0) hfm.aestronglyMeasurable, hint, ← hmeas,
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hκ0.le, ENNReal.coe_toReal]
  have e : 1 / (κ * cH) * (κ * cH * (μH[((2 * (d + 1) : ℕ) : ℝ)] (zeroSetEuc J ∩ B)).toReal) =
      (μH[((2 * (d + 1) : ℕ) : ℝ)] (zeroSetEuc J ∩ B)).toReal := by
    field_simp
  rw [e, ENNReal.ofReal_toReal hfin.ne]

end

end GroundTheory.Heights₂.Heights
