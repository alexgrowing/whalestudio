import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPowerBlockMeasure
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPowerBlockPointNorm
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPowerBlockOldPartSurj
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPrimeZariskiDense
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory
open scoped ENNReal

noncomputable section

set_option linter.unusedSectionVars false

namespace PowerBlockMeasure

section Cone

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isOpen_nz : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  simp only [Set.ofPred_forall, Set.ofPred_exists]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

theorem measurableSet_mcPts (P : Ideal (MRing ι)) : MeasurableSet (mcPts P) := by
  have hcl : IsClosed {z : (Σ k, ι k) → ℂ | ∀ f ∈ P, eval z (map (Int.castRingHom ℂ) f) = 0} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun f => isClosed_iInter fun _ => isClosed_eq (continuous_eval _) continuous_const
  exact isOpen_nz.measurableSet.inter hcl.measurableSet

theorem eval_smul_homogC (g : MvPolynomial (Σ k, ι k) ℂ) (d : K → ℕ) (hg : IsMultiHomog g d) (c : K → ℂ)
    (z : (Σ k, ι k) → ℂ) :
    eval (fun p => c p.1 * z p) g = (∏ k, c k ^ d k) * eval z g := by
  rw [eval_eq', eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  have hc : (∏ i : (Σ k, ι k), c i.1 ^ e i) = ∏ k, c k ^ d k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ y, c k ^ e ⟨k, y⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hg e he k]
  simp only [mul_pow, Finset.prod_mul_distrib, hc]
  ring

theorem isMultiHomog_map {F : MRing ι} {d : K → ℕ} (hF : IsMultiHomog F d) :
    IsMultiHomog (map (Int.castRingHom ℂ) F) d :=
  fun e he => hF e (support_map_subset _ _ he)

theorem eval_conjPt_map (z : (Σ k, ι k) → ℂ) (f : MRing ι) :
    eval (conjPt z) (map (Int.castRingHom ℂ) f) = starRingEnd ℂ (eval z (map (Int.castRingHom ℂ) f)) := by
  rw [eval_map, eval_map, eval₂_comp_left]
  congr 1
  exact RingHom.ext_int _ _

theorem continuous_conjPt' : Continuous (conjPt : ((Σ k, ι k) → ℂ) → (Σ k, ι k) → ℂ) :=
  continuous_pi fun p => Complex.continuous_conj.comp (continuous_apply p)

theorem conjPt_mem {P : Ideal (MRing ι)} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) : conjPt z ∈ mcPts P := by
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i, hi⟩ := hz.1 k
    exact ⟨i, by simpa [conjPt] using hi⟩
  · rw [eval_conjPt_map, hz.2 f hf, map_zero]

theorem sameOrbit_conj {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') : SameOrbit (conjPt z) (conjPt z') := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => starRingEnd ℂ (c k), fun k => (map_ne_zero _).2 (hc k), ?_⟩
  funext p
  simp [conjPt]

end Cone

section Block

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] {N : ℕ}

def oldV (p : Σ k, ι k) : Σ k, addIdx ι N k := ⟨some p.1, p.2⟩

theorem measurable_oldPart : Measurable (basePart₂ : ((Σ k, addIdx ι N k) → ℂ) → (Σ k, ι k) → ℂ) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _

theorem continuous_oldPart : Continuous (basePart₂ : ((Σ k, addIdx ι N k) → ℂ) → (Σ k, ι k) → ℂ) :=
  continuous_pi fun _ => continuous_apply _

theorem rename_old_mem (y : (Σ k, ι k) → Ω) (v : Fin N → Ω) {f : MRing ι} (hf : f ∈ mCoordIdeal y) :
    rename (oldV (N := N)) f ∈ mCoordIdeal (addBlock y v) := by
  have key : (mConeMap (addBlock y v)).comp (rename (oldV (N := N))) =
      ((rename (some : K → Option K)).restrictScalars ℤ).comp (mConeMap y) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [mConeMap, oldV, addBlock]
  have h := congrArg (fun φ => φ f) key
  simp only [AlgHom.comp_apply] at h
  show mConeMap (addBlock y v) (rename oldV f) = 0
  rw [h]
  have : mConeMap y f = 0 := hf
  rw [this, map_zero]

theorem oldPart_mem {y : (Σ k, ι k) → Ω} {v : Fin N → Ω} {z : (Σ k, addIdx ι N k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal (addBlock y v))) : basePart₂ z ∈ mcPts (mCoordIdeal y) := by
  refine ⟨fun k => hz.1 (some k), fun f hf => ?_⟩
  have h := hz.2 _ (rename_old_mem y v hf)
  rwa [map_rename, eval_rename] at h

theorem eval_oldPart_orbit {g : MvPolynomial (Σ k, ι k) ℂ} {d : K → ℕ} (hg : IsMultiHomog g d)
    {z z' : (Σ k, addIdx ι N k) → ℂ} (h : SameOrbit z z') :
    ∃ u : ℂ, u ≠ 0 ∧ eval (basePart₂ z) g = u * eval (basePart₂ z') g := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨∏ k, c (some k) ^ d k, Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc _), ?_⟩
  exact eval_smul_homogC g d hg (fun k => c (some k)) (basePart₂ z')

end Block

section Resolution

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)} {e : ℕ}

theorem continuousOn_lift (R : AnRes P J e) (x₀ : R.X) : ContinuousOn (R.lift x₀) (R.U x₀) := by
  refine continuousOn_pi.2 fun p => ?_
  intro z hz
  obtain ⟨j, hj⟩ := R.A.cover z
  have hzt : R.A.chart j z ∈ (R.A.chart j).target := (R.A.chart j).map_source hj
  have hc : ContinuousAt ((fun z => R.lift x₀ z p) ∘ (R.A.chart j).symm) (R.A.chart j z) :=
    (R.holo x₀ p j _ ⟨hzt, by rwa [Set.mem_preimage, (R.A.chart j).left_inv hj]⟩).continuousAt
  have h := ((R.A.chart j).symm.continuousAt_iff_continuousAt_comp_right
    (f := fun z => R.lift x₀ z p) (x := z) (by simpa using hj)).mpr (by simpa using hc)
  exact h.continuousWithinAt

theorem continuous_orbitFun (R : AnRes P J e) {β : Type*} [TopologicalSpace β] {g : ((Σ k, ι k) → ℂ) → β}
    (hgc : ContinuousOn g {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}) (hg : ∀ z z', SameOrbit z z' → g z = g z') :
    Continuous fun x => g (R.lift x x) := by
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  have hU := (R.isOpen_U x₀).mem_nhds (R.mem_U x₀)
  have h1 : ContinuousAt (R.lift x₀) x₀ := (continuousOn_lift R x₀).continuousAt hU
  have h2 : ContinuousAt (fun x => g (R.lift x₀ x)) x₀ :=
    (hgc.continuousAt (isOpen_nz.mem_nhds (R.mem x₀ x₀ (R.mem_U x₀)).1)).comp h1
  refine h2.congr ?_
  filter_upwards [hU] with x hx
  exact hg _ _ (R.compat x₀ x x ⟨hx, R.mem_U x⟩)

theorem exists_measurable_lift (R : AnRes P J e) [MeasurableSpace R.X] [BorelSpace R.X] :
    ∃ φ : R.X → (Σ k, ι k) → ℂ, Measurable φ ∧ ∀ x, ∃ x₀, x ∈ R.U x₀ ∧ φ x = R.lift x₀ x := by
  classical
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x₀ : R.X => R.U x₀) R.isOpen_U
    fun x _ => Set.mem_iUnion.2 ⟨x, R.mem_U x⟩
  have key : ∀ l : List R.X, ∃ φ : R.X → (Σ k, ι k) → ℂ, Measurable φ ∧
      ∀ x, (∃ x₀ ∈ l, x ∈ R.U x₀) → ∃ x₀, x ∈ R.U x₀ ∧ φ x = R.lift x₀ x := by
    intro l
    induction l with
    | nil => exact ⟨fun _ => 0, measurable_const, fun x ⟨_, h, _⟩ => absurd h List.not_mem_nil⟩
    | cons x₀ l ih =>
      obtain ⟨φ, hφm, hφ⟩ := ih
      refine ⟨(R.U x₀).piecewise ((R.U x₀).piecewise (R.lift x₀) fun _ => 0) φ, ?_, ?_⟩
      · exact Measurable.piecewise (R.isOpen_U x₀).measurableSet
          ((continuousOn_lift R x₀).measurable_piecewise continuousOn_const (R.isOpen_U x₀).measurableSet) hφm
      · intro x hx
        by_cases hxU : x ∈ R.U x₀
        · exact ⟨x₀, hxU, by simp [Set.piecewise, hxU]⟩
        · obtain ⟨x₁, hx₁, hxx⟩ := hx
          rcases List.mem_cons.1 hx₁ with rfl | h
          · exact absurd hxx hxU
          · obtain ⟨x₂, hx₂, he⟩ := hφ x ⟨x₁, h, hxx⟩
            exact ⟨x₂, hx₂, by simp [Set.piecewise, hxU, he]⟩
  obtain ⟨φ, hφm, hφ⟩ := key t.toList
  refine ⟨φ, hφm, fun x => hφ x ?_⟩
  obtain ⟨x₀, hx₀t, hx₀U⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
  exact ⟨x₀, Finset.mem_toList.2 hx₀t, hx₀U⟩

theorem dV_pos_of_isOpen (R : AnRes P J e) [MeasurableSpace R.X] [BorelSpace R.X] {dV : Measure R.X}
    (hV : IsSmoothVolume R.A dV) {S : Set R.X} (hS : IsOpen S) (hne : S.Nonempty) : 0 < dV S := by
  obtain ⟨y, hy⟩ := hne
  obtain ⟨j, hj⟩ := R.A.cover y
  obtain ⟨ν, hνc, hνp, hν⟩ := hV.2 j
  set S' := S ∩ (R.A.chart j).source with hS'
  have hS'o : IsOpen S' := hS.inter (R.A.chart j).open_source
  set T := (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' S' with hT
  have hTo : IsOpen T := (R.A.chart j).isOpen_inter_preimage_symm hS'o
  have hTy : R.A.chart j y ∈ T :=
    ⟨(R.A.chart j).map_source hj, by simp [(R.A.chart j).left_inv hj, hS', hy, hj]⟩
  have hvol : 0 < volume T := hTo.measure_pos volume ⟨_, hTy⟩
  have hmono : dV S' ≤ dV S := measure_mono Set.inter_subset_left
  refine lt_of_lt_of_le ?_ hmono
  rw [hν S' hS'o.measurableSet Set.inter_subset_right]
  have hae : AEMeasurable (fun w => ENNReal.ofReal (ν w)) (volume.restrict T) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      ((hνc.continuousOn.mono Set.inter_subset_left).aemeasurable hTo.measurableSet)
  refine pos_iff_ne_zero.2 fun h0 => ?_
  rw [lintegral_eq_zero_iff' hae] at h0
  have h0' : ∀ᵐ w ∂(volume.restrict T), ENNReal.ofReal (ν w) = 0 := h0
  rw [ae_iff] at h0'
  have : volume.restrict T T = 0 := by
    refine measure_mono_null (fun w hw => ?_) h0'
    simp only [Set.mem_ofPred_eq, ENNReal.ofReal_eq_zero, not_le]
    exact hνp w hw.1
  rw [Measure.restrict_apply_self] at this
  exact hvol.ne' this

end Resolution

theorem aesm_map {α V : Type*} [MeasurableSpace α] [TopologicalSpace V] [MeasurableSpace V] [OpensMeasurableSpace V]
    {μ : Measure α} {h : α → V} (hh : Measurable h) {T : Set V} (hT : MeasurableSet T) (hhT : ∀ x, h x ∈ T)
    {g : V → ℝ} (hg : ContinuousOn g T) : AEStronglyMeasurable g (μ.map h) := by
  classical
  have hG : Measurable (T.piecewise g fun _ => 0) := hg.measurable_piecewise continuousOn_const hT
  have h0 : μ.map h Tᶜ = 0 := by
    rw [Measure.map_apply hh hT.compl]
    have : h ⁻¹' Tᶜ = ∅ := by
      ext x
      simp [hhT x]
    rw [this, measure_empty]
  refine hG.aestronglyMeasurable.congr (ae_iff.2 (measure_mono_null (fun z hz => ?_) h0))
  intro hzT
  exact hz (Set.piecewise_eq_of_mem _ _ _ hzT)

end PowerBlockMeasure

open PowerBlockMeasure in

theorem PowerBlockMeasure.proof (hPN : PowerBlockPointNorm.Statement) (hOS : PowerBlockOldPartSurj.Statement)
    (hZD : PrimeZariskiDense.Statement) : PowerBlockMeasure.Statement := by
  intro K _ _ ι _ Ω _ y A m N D v B J R _ _ dV hA hB hBa hV hv hgen hrel
  classical
  have := hV.1
  obtain ⟨φ, hφm, hφ⟩ := exists_measurable_lift R
  have hφP : ∀ x, φ x ∈ mcPts (mCoordIdeal (addBlock y v)) := fun x => by
    obtain ⟨x₀, hx, he⟩ := hφ x
    rw [he]
    exact R.mem x₀ x hx
  have hφO : ∀ x, SameOrbit (φ x) (R.lift x x) := fun x => by
    obtain ⟨x₀, hx, he⟩ := hφ x
    rw [he]
    exact R.compat x₀ x x ⟨hx, R.mem_U x⟩
  set ψ : R.X → (Σ k, ι k) → ℂ := fun x => basePart₂ (φ x) with hψdef
  have hψm : Measurable ψ := measurable_oldPart.comp hφm
  have hcm : Measurable (conjPt ∘ ψ) := continuous_conjPt'.measurable.comp hψm
  have hψP : ∀ x, ψ x ∈ mcPts (mCoordIdeal y) := fun x => oldPart_mem (hφP x)
  have hcP : ∀ x, (conjPt ∘ ψ) x ∈ mcPts (mCoordIdeal y) := fun x => conjPt_mem (hψP x)
  have hT := measurableSet_mcPts (mCoordIdeal y)
  refine ⟨(2⁻¹ : ℝ≥0∞) • (dV.map ψ + dV.map (conjPt ∘ ψ)), ?_, ?_, ?_, ?_⟩
  ·
    constructor
    rw [Measure.smul_apply, Measure.add_apply, Measure.map_apply hψm MeasurableSet.univ,
      Measure.map_apply hcm MeasurableSet.univ, Set.preimage_univ, Set.preimage_univ, measure_univ, smul_eq_mul,
      one_add_one_eq_two, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]
  ·
    rw [Measure.smul_apply, Measure.add_apply, Measure.map_apply hψm hT.compl, Measure.map_apply hcm hT.compl]
    have h1 : ψ ⁻¹' (mcPts (mCoordIdeal y))ᶜ = ∅ := by
      ext x
      simp [hψP x]
    have h2 : (conjPt ∘ ψ) ⁻¹' (mcPts (mCoordIdeal y))ᶜ = ∅ := by
      ext x
      simpa using hcP x
    rw [h1, h2, measure_empty, add_zero, smul_zero]
  ·
    intro d f hf hae

    have h1 : dV {x | ¬ eval (ψ x) f = 0} = 0 := by
      have hS0 := ae_iff.1 hae
      rw [Measure.smul_apply, Measure.add_apply, smul_eq_mul, mul_eq_zero, add_eq_zero] at hS0
      have hS1 : dV.map ψ {z | ¬ eval z f = 0} = 0 := by
        rcases hS0 with h | h
        · exact absurd h (by simp)
        · exact h.1
      exact ae_iff.1 (ae_of_ae_map hψm.aemeasurable (ae_iff.2 hS1))

    have h2 : ∀ x, eval (basePart₂ (R.lift x x)) f = 0 := by
      set S := {x | eval (basePart₂ (R.lift x x)) f ≠ 0} with hSdef
      have hSo : IsOpen S := by
        rw [isOpen_iff_mem_nhds]
        intro x₀ hx₀
        have hU := (R.isOpen_U x₀).mem_nhds (R.mem_U x₀)
        have hc : ContinuousAt (fun x => eval (basePart₂ (R.lift x₀ x)) f) x₀ :=
          (continuous_eval f).continuousAt.comp
            (continuous_oldPart.continuousAt.comp ((continuousOn_lift R x₀).continuousAt hU))
        obtain ⟨u, hu, hue⟩ := eval_oldPart_orbit hf (R.compat x₀ x₀ x₀ ⟨R.mem_U x₀, R.mem_U x₀⟩)
        have hne : eval (basePart₂ (R.lift x₀ x₀)) f ≠ 0 := by
          rw [hue]
          exact mul_ne_zero hu hx₀
        filter_upwards [hU, hc.eventually_ne hne] with x hx hx'
        obtain ⟨u', hu', hue'⟩ := eval_oldPart_orbit hf (R.compat x₀ x x ⟨hx, R.mem_U x⟩)
        intro h0
        apply hx'
        rw [hue', h0, mul_zero]
      have hSnull : dV S = 0 := by
        refine measure_mono_null (fun x hx => ?_) h1
        obtain ⟨u, hu, hue⟩ := eval_oldPart_orbit hf (hφO x)
        intro h0
        apply hx
        have : u * eval (basePart₂ (R.lift x x)) f = 0 := by rw [← hue]; exact h0
        exact (mul_eq_zero.1 this).resolve_left hu
      intro x
      by_contra hx
      exact (dV_pos_of_isOpen R hV hSo ⟨x, hx⟩).ne' hSnull

    have h3 : ∀ z ∈ mcPts (mCoordIdeal (addBlock y v)), z ∉ mcPts J → eval (basePart₂ z) f = 0 := by
      intro z hz hzJ
      obtain ⟨x, hx⟩ := R.surj z hz hzJ
      obtain ⟨u, hu, hue⟩ := eval_oldPart_orbit hf hx
      have := h2 x
      rw [hue] at this
      exact (mul_eq_zero.1 this).resolve_left hu

    have hprime : (mCoordIdeal (addBlock y v)).IsPrime := RingHom.ker_isPrime _
    obtain ⟨j, hjJ, hjP⟩ := SetLike.not_le_iff_exists.1 R.nondeg
    have h4 : ∀ z ∈ mcPts (mCoordIdeal (addBlock y v)), eval (basePart₂ z) f = 0 := by
      intro z hz
      have := hZD (Option K) (addIdx ι N) (mCoordIdeal (addBlock y v)) j hprime hjP
        (rename (oldV (ι := ι) (N := N)) f) (fun z' hz' hj => ?_) z hz
      · rwa [eval_rename] at this
      · rw [eval_rename]
        exact h3 z' hz' fun hzJ => hj (hzJ.2 j hjJ)

    intro x hx
    obtain ⟨z, hz, rfl⟩ := hOS K ι Ω y A.a m N v hv hgen x hx
    exact h4 z hz
  ·
    intro q F hF
    obtain ⟨hcont, hpt⟩ := hPN K ι Ω y A m N v B hA.continuousOn hBa hv hrel q F hF
    have hFC := isMultiHomog_map hF
    set Φ : ((Σ k, addIdx ι N k) → ℂ) → ℝ :=
      fun z => (‖eval z (map (Int.castRingHom ℂ) F)‖ / B.h z ^ q) ^ 2 with hΦdef
    have hΦinv : ∀ z z', SameOrbit z z' → Φ z = Φ z' := by
      rintro _ z' ⟨c, hc, rfl⟩
      have hF' : eval (fun p => c p.1 * z' p) (map (Int.castRingHom ℂ) F) =
          c none ^ q * eval z' (map (Int.castRingHom ℂ) F) := by
        rw [eval_smul_homogC _ _ hFC c z', Finset.prod_eq_single (none : Option K)]
        · simp [blockDeg]
        · intro k _ hk
          simp [blockDeg, hk]
        · simp
      have hB' : B.h (fun p => c p.1 * z' p) = ‖c none‖ * B.h z' := by
        rw [B.smul c z' hc, hBa, Finset.prod_eq_single (none : Option K)]
        · simp [unitDeg]
        · intro k _ hk
          simp [unitDeg, hk]
        · simp
      have hcn : ‖c none‖ ^ q ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 (hc none))
      simp only [hΦdef, hF', hB', norm_mul, norm_pow, mul_pow]
      rw [mul_div_mul_left _ _ hcn]
    have hΦc : ContinuousOn Φ {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
      refine ContinuousOn.pow (ContinuousOn.div (continuous_eval _).norm.continuousOn
        (hB.continuousOn.pow q) fun z hz => pow_ne_zero _ (B.pos z hz).ne') 2
    have hc1 : Continuous fun x => Φ (R.lift x x) := continuous_orbitFun R hΦc hΦinv
    have hc2 : Continuous fun x => Φ (conjPt (R.lift x x)) := by
      refine continuous_orbitFun R (g := fun z => Φ (conjPt z))
        (hΦc.comp continuous_conjPt'.continuousOn fun z hz k => ?_) fun z z' h => hΦinv _ _ (sameOrbit_conj h)
      obtain ⟨i, hi⟩ := hz k
      exact ⟨i, by simpa [conjPt] using hi⟩
    set s := aeval (addBlock y v) F
    set g : ((Σ k, ι k) → ℂ) → ℝ := fun x => secNormAt y A (m * q) s x ^ 2 with hgdef
    have hg1 : ∀ x, g (ψ x) = Φ (R.lift x x) := fun x => by
      simp only [hgdef, hψdef]
      rw [hpt _ (hφP x)]
      exact hΦinv _ _ (hφO x)
    have hg2 : ∀ x, g ((conjPt ∘ ψ) x) = Φ (conjPt (R.lift x x)) := fun x => by
      have e : (conjPt ∘ ψ) x = basePart₂ (conjPt (φ x)) := rfl
      simp only [hgdef]
      rw [e, hpt _ (conjPt_mem (hφP x))]
      exact hΦinv _ _ (sameOrbit_conj (hφO x))
    have hgc : ContinuousOn g (mcPts (mCoordIdeal y)) := hcont.pow 2
    have hgm1 : AEStronglyMeasurable g (dV.map ψ) := aesm_map hψm hT hψP hgc
    have hgm2 : AEStronglyMeasurable g (dV.map (conjPt ∘ ψ)) := aesm_map hcm hT hcP hgc
    have hi1 : Integrable (fun x => Φ (R.lift x x)) dV :=
      integrableOn_univ.1 (hc1.continuousOn.integrableOn_compact isCompact_univ)
    have hi2 : Integrable (fun x => Φ (conjPt (R.lift x x))) dV :=
      integrableOn_univ.1 (hc2.continuousOn.integrableOn_compact isCompact_univ)
    have hI1 : Integrable g (dV.map ψ) := by
      rw [integrable_map_measure hgm1 hψm.aemeasurable]
      have : g ∘ ψ = fun x => Φ (R.lift x x) := funext hg1
      rw [this]
      exact hi1
    have hI2 : Integrable g (dV.map (conjPt ∘ ψ)) := by
      rw [integrable_map_measure hgm2 hcm.aemeasurable]
      have : g ∘ (conjPt ∘ ψ) = fun x => Φ (conjPt (R.lift x x)) := funext hg2
      rw [this]
      exact hi2
    show Real.sqrt (∫ z, g z ∂((2⁻¹ : ℝ≥0∞) • (dV.map ψ + dV.map (conjPt ∘ ψ)))) = _
    rw [integral_smul_measure, integral_add_measure hI1 hI2, integral_map hψm.aemeasurable hgm1,
      integral_map hcm.aemeasurable hgm2]
    simp only [hg1, hg2, hΦdef]
    rw [ENNReal.toReal_inv, ENNReal.toReal_ofNat, smul_eq_mul, one_div]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
