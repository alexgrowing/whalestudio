import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.EmDefs

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ComplexConjugate

namespace GlobalTheory.CompanionTheory.EisDens

theorem sw_bump {X : Type} [TopologicalSpace X] [T2Space X] (A : Submodule ℂ (X → ℂ))
    (hA : PositivityTheory.Rg.Rsw.Em.Rich A) (f : X → ℂ) (hf : Continuous f) (hc : HasCompactSupport f) :
    ∃ b ∈ A, (∀ x, 0 ≤ (b x).re ∧ (b x).im = 0) ∧
      ∀ ε : ℝ, 0 < ε → ∃ h ∈ A, ∀ z, ‖f z - h z‖ ≤ ε * (b z).re := by
  obtain ⟨b, hbA, hb0, hb1⟩ := hA.bump (tsupport f) hc.isCompact
  refine ⟨b, hbA, hb0, fun ε hε => ?_⟩
  have hbK : IsCompact (tsupport b) := (hA.cc b hbA).2.isCompact
  haveI : CompactSpace (tsupport b) := isCompact_iff_compactSpace.mp hbK
  let S : StarSubalgebra ℂ C(tsupport b, ℂ) :=
    { carrier := {u | ∃ a ∈ A, ∃ c : ℂ, ∀ x : tsupport b, u x = a x + c}
      mul_mem' := by
        rintro u u' ⟨a, ha, c, hu⟩ ⟨a', ha', c', hu'⟩
        refine ⟨a * a' + c • a' + c' • a, A.add_mem (A.add_mem (hA.mul a ha a' ha') (A.smul_mem c ha'))
          (A.smul_mem c' ha), c * c', fun x => ?_⟩
        simp only [ContinuousMap.mul_apply, hu, hu', Pi.add_apply, Pi.mul_apply, Pi.smul_apply,
          smul_eq_mul]
        ring
      one_mem' := ⟨0, A.zero_mem, 1, by simp⟩
      add_mem' := by
        rintro u u' ⟨a, ha, c, hu⟩ ⟨a', ha', c', hu'⟩
        refine ⟨a + a', A.add_mem ha ha', c + c', fun x => ?_⟩
        simp only [ContinuousMap.add_apply, hu, hu', Pi.add_apply]
        ring
      zero_mem' := ⟨0, A.zero_mem, 0, by simp⟩
      algebraMap_mem' := fun c => ⟨0, A.zero_mem, c, by simp [algebraMap_apply]⟩
      star_mem' := by
        rintro u ⟨a, ha, c, hu⟩
        refine ⟨star a, hA.star a ha, star c, fun x => ?_⟩
        simp [hu] }
  have hsep : S.SeparatesPoints := by
    intro p q hpq
    obtain ⟨a, ha, hne⟩ := hA.sep p.1 q.1 (fun h => hpq (Subtype.ext h))
    have hac := (hA.cc a ha).1
    refine ⟨_, ⟨⟨fun x => a x.1, hac.comp continuous_subtype_val⟩, ⟨a, ha, 0, fun x => by simp⟩, rfl⟩, ?_⟩
    exact hne
  have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints S hsep
  let fK : C(tsupport b, ℂ) := ⟨fun x => f x.1, hf.comp continuous_subtype_val⟩
  have hfmem : fK ∈ closure (S : Set C(tsupport b, ℂ)) := by
    have : fK ∈ S.topologicalClosure := by rw [htop]; trivial
    exact this
  obtain ⟨u, ⟨a, ha, c, hu⟩, hfu⟩ := Metric.mem_closure_iff.1 hfmem ε hε
  refine ⟨b * a + c • b, A.add_mem (hA.mul b hbA a ha) (A.smul_mem c hbA), fun z => ?_⟩
  have hbf : f z = b z * f z := by
    by_cases hz : z ∈ tsupport f
    · rw [hb1 z hz, one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hz, mul_zero]
  have hbr : b z = ((b z).re : ℂ) := by
    apply Complex.ext <;> simp [(hb0 z).2]
  have e : f z - (b * a + c • b) z = b z * (f z - (a z + c)) := by
    simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    rw [mul_sub, ← hbf]
    ring
  rw [e, norm_mul]
  by_cases hz : z ∈ tsupport b
  · have h1 : ‖f z - (a z + c)‖ ≤ ε := by
      have := (ContinuousMap.dist_apply_le_dist (f := fK) (g := u) ⟨z, hz⟩).trans hfu.le
      rw [dist_eq_norm, hu] at this
      exact this
    have h2 : ‖b z‖ = (b z).re := by
      rw [hbr, Complex.norm_real, Real.norm_of_nonneg (hb0 z).1]
      simp
    rw [h2, mul_comm]
    exact mul_le_mul_of_nonneg_right h1 (hb0 z).1
  · have h0 : b z = 0 := image_eq_zero_of_notMem_tsupport hz
    simp [h0]

theorem approx_tendsto {X : Type} [MeasurableSpace X] (m : ℕ → Measure X) (ν : Measure X)
    (f : X → ℂ) (b : X → ℝ) (c : ℝ) (hf : ∀ j, Integrable f (m j)) (hb : ∀ j, Integrable b (m j))
    (hbc : Tendsto (fun j => ∫ z, b z ∂m j) atTop (𝓝 c)) (hfν : Integrable f ν) (hbν : Integrable b ν)
    (happ : ∀ ε : ℝ, 0 < ε → ∃ f₁ : X → ℂ, (∀ j, Integrable f₁ (m j)) ∧ Integrable f₁ ν ∧
      Tendsto (fun j => ∫ z, f₁ z ∂m j) atTop (𝓝 (∫ z, f₁ z ∂ν)) ∧ ∀ z, ‖f z - f₁ z‖ ≤ ε * b z) :
    Tendsto (fun j => ∫ z, f z ∂m j) atTop (𝓝 (∫ z, f z ∂ν)) := by
  rw [Metric.tendsto_atTop]
  intro δ hδ
  set c' := ∫ z, b z ∂ν with hc'
  set B := |c| + |c'| + 1 with hBdef
  have hB : 0 < B := by positivity
  obtain ⟨f₁, h1, h2, h3, h4⟩ := happ (δ / (3 * B)) (by positivity)
  set ε := δ / (3 * B) with hεdef
  have hε : 0 < ε := by positivity
  have hεB : ε * B = δ / 3 := by
    rw [hεdef]; field_simp
  have hbd : ∀ μ : Measure X, Integrable f μ → Integrable f₁ μ → Integrable b μ →
      ‖∫ z, f z ∂μ - ∫ z, f₁ z ∂μ‖ ≤ ε * ∫ z, b z ∂μ := by
    intro μ a1 a2 a3
    rw [← integral_sub a1 a2, ← integral_const_mul]
    exact norm_integral_le_of_norm_le (a3.const_mul ε) (Eventually.of_forall h4)
  have ev1 : ∀ᶠ j in atTop, ∫ z, b z ∂m j < c + 1 := hbc.eventually_lt_const (lt_add_one c)
  have ev2 : ∀ᶠ j in atTop, dist (∫ z, f₁ z ∂m j) (∫ z, f₁ z ∂ν) < δ / 3 :=
    (Metric.tendsto_nhds.1 h3) _ (by positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (ev1.and ev2)
  refine ⟨N, fun j hj => ?_⟩
  obtain ⟨e1, e2⟩ := hN j hj
  have a1 := hbd (m j) (hf j) (h1 j) (hb j)
  have a2 := hbd ν hfν h2 hbν
  rw [dist_eq_norm] at e2 ⊢
  have tri : ‖∫ z, f z ∂m j - ∫ z, f z ∂ν‖ ≤ ‖∫ z, f z ∂m j - ∫ z, f₁ z ∂m j‖ +
      ‖∫ z, f₁ z ∂m j - ∫ z, f₁ z ∂ν‖ + ‖∫ z, f z ∂ν - ∫ z, f₁ z ∂ν‖ := by
    have e : ∫ z, f z ∂m j - ∫ z, f z ∂ν = (∫ z, f z ∂m j - ∫ z, f₁ z ∂m j) +
      (∫ z, f₁ z ∂m j - ∫ z, f₁ z ∂ν) - (∫ z, f z ∂ν - ∫ z, f₁ z ∂ν) := by ring
    rw [e]
    exact (norm_sub_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
  have b1 : ε * ∫ z, b z ∂m j ≤ ε * B := by
    refine mul_le_mul_of_nonneg_left ?_ hε.le
    have := le_abs_self c
    have := abs_nonneg c'
    rw [hBdef]; linarith
  have b2 : ε * c' ≤ ε * B := by
    refine mul_le_mul_of_nonneg_left ?_ hε.le
    have := le_abs_self c'
    have := abs_nonneg c
    rw [hBdef]; linarith
  linarith

theorem null_of_test {X : Type} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] (ν : Measure X)
    [IsFiniteMeasureOnCompacts ν] (U : Set X) (hU : IsOpen U)
    (h : ∀ c : X → ℝ, Continuous c → HasCompactSupport c → (∀ z, 0 ≤ c z) → tsupport c ⊆ U →
      ∫ z, c z ∂ν = 0) : ν U = 0 := by
  have hK : ∀ K : Set X, IsCompact K → K ⊆ U → ν K = 0 := by
    intro K hK hKU
    obtain ⟨φ, h1, h2, h3, h4⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hK hU hKU
    have hcs : HasCompactSupport φ := h2
    have h0 : ∀ z, 0 ≤ φ z := fun z => (h4 z).1
    have hi : Integrable φ ν := φ.continuous.integrable_of_hasCompactSupport hcs
    have hz := h φ φ.continuous hcs h0 h3
    have hae := (integral_eq_zero_iff_of_nonneg h0 hi).1 hz
    refine measure_mono_null (t := {z | ¬ φ z = (0 : X → ℝ) z}) (fun z hzK => ?_) (ae_iff.1 hae)
    have : φ z = 1 := h1 hzK
    simp [this]
  have hc : ∀ x : U, ∃ K, IsCompact K ∧ x.1 ∈ interior K ∧ K ⊆ U := fun x => exists_compact_subset hU x.2
  choose K h1 h2 h3 using hc
  obtain ⟨T, hT, hTe⟩ := TopologicalSpace.isOpen_iUnion_countable (fun x => interior (K x))
    (fun x => isOpen_interior)
  have hsub : U ⊆ ⋃ x ∈ T, K x := by
    intro z hz
    have hz' : z ∈ ⋃ x, interior (K x) := Set.mem_iUnion.2 ⟨⟨z, hz⟩, h2 _⟩
    rw [← hTe] at hz'
    simp only [Set.mem_iUnion] at hz' ⊢
    obtain ⟨x, hx, hzx⟩ := hz'
    exact ⟨x, hx, interior_subset hzx⟩
  exact measure_mono_null hsub ((measure_biUnion_null_iff hT).2 fun x _ => hK _ (h1 x) (h3 x))

theorem lintegral_le_of_minor {X : Type} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] (ν : Measure X)
    [IsFiniteMeasureOnCompacts ν] (b : X → ℝ) (hb : Continuous b) (hb0 : ∀ z, 0 ≤ b z) (M : ℝ)
    (hM : ∀ c : X → ℝ, Continuous c → HasCompactSupport c → (∀ z, 0 ≤ c z) → (∀ z, c z ≤ b z) →
      ∫ z, c z ∂ν ≤ M) :
    ∫⁻ z, ENNReal.ofReal (b z) ∂ν ≤ ENNReal.ofReal M := by
  let E := CompactExhaustion.choice X
  have hφ : ∀ n, ∃ φ : C(X, ℝ), Set.EqOn φ 1 (E n) ∧ IsCompact (tsupport φ) ∧ tsupport φ ⊆ Set.univ ∧
      ∀ x, φ x ∈ Set.Icc (0 : ℝ) 1 := fun n =>
    exists_continuousMap_one_of_isCompact_subset_isOpen (E.isCompact n) isOpen_univ (Set.subset_univ _)
  choose φ h1 h2 _ h4 using hφ
  let c : ℕ → X → ℝ := fun n z => φ n z * b z
  have hcc : ∀ n, Continuous (c n) := fun n => (φ n).continuous.mul hb
  have hcs : ∀ n, HasCompactSupport (c n) := fun n => HasCompactSupport.mul_right (h2 n)
  have hc0 : ∀ n z, 0 ≤ c n z := fun n z => mul_nonneg (h4 n z).1 (hb0 z)
  have hcb : ∀ n z, c n z ≤ b z := fun n z => mul_le_of_le_one_left (hb0 z) (h4 n z).2
  have hlim : ∀ z, Tendsto (fun n => ENNReal.ofReal (c n z)) atTop (𝓝 (ENNReal.ofReal (b z))) := by
    intro z
    obtain ⟨n₀, hn₀⟩ := E.exists_mem z
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop n₀] with n hn
    have : φ n z = 1 := h1 n (E.subset hn hn₀)
    simp [c, this]
  have hle : ∀ n, ∫⁻ z, ENNReal.ofReal (c n z) ∂ν ≤ ENNReal.ofReal M := by
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal ((hcc n).integrable_of_hasCompactSupport (hcs n))
      (Eventually.of_forall (hc0 n))]
    exact ENNReal.ofReal_le_ofReal (hM _ (hcc n) (hcs n) (hc0 n) (hcb n))
  calc ∫⁻ z, ENNReal.ofReal (b z) ∂ν = ∫⁻ z, liminf (fun n => ENNReal.ofReal (c n z)) atTop ∂ν :=
        lintegral_congr fun z => (hlim z).liminf_eq.symm
    _ ≤ liminf (fun n => ∫⁻ z, ENNReal.ofReal (c n z) ∂ν) atTop :=
        lintegral_liminf_le fun n => (hcc n).measurable.ennreal_ofReal
    _ ≤ ENNReal.ofReal M := by
        refine (liminf_le_liminf (Eventually.of_forall hle)).trans ?_
        simp

section Seq
variable {X N : Type} [MeasurableSpace X] [MeasurableSpace N] {lam : Measure N} [SFinite lam]
  {k : N → X → ℂ}

theorem H_sm (g : N → ℂ) (hg : Integrable g lam) (hk : Measurable (Function.uncurry k)) :
    StronglyMeasurable (fun z => ∫ x, g x * k x z ∂lam) := by
  have hg' := hg.aestronglyMeasurable
  have e : (fun z => ∫ x, g x * k x z ∂lam) = fun z => ∫ x, hg'.mk g x * k x z ∂lam := by
    funext z
    refine integral_congr_ae ?_
    filter_upwards [hg'.ae_eq_mk] with x hx
    rw [hx]
  rw [e]
  refine StronglyMeasurable.integral_prod_right (f := fun z x => hg'.mk g x * k x z) ?_
  have h1 : Measurable fun u : X × N => hg'.mk g u.2 :=
    hg'.stronglyMeasurable_mk.measurable.comp measurable_snd
  have h2 : Measurable fun u : X × N => k u.2 u.1 := hk.comp measurable_swap
  exact (h1.mul h2).stronglyMeasurable

theorem H_bd (g : N → ℂ) (hg : Integrable g lam) (hk1 : ∀ x z, ‖k x z‖ ≤ 1) (z : X) :
    ‖∫ x, g x * k x z ∂lam‖ ≤ ∫ x, ‖g x‖ ∂lam :=
  norm_integral_le_of_norm_le hg.norm (Eventually.of_forall fun x => by
    rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) (hk1 x z))

theorem fub (σ : Measure X) [SFinite σ] (g : N → ℂ) (f : X → ℂ) (hg : Integrable g lam)
    (hf : Integrable f σ) (hk : Measurable (Function.uncurry k)) (hk1 : ∀ x z, ‖k x z‖ ≤ 1) :
    ∫ x, g x * ∫ z, f z * k x z ∂σ ∂lam = ∫ z, f z * (∫ x, g x * k x z ∂lam) ∂σ := by
  have h0 : Integrable (fun u : N × X => g u.1 * f u.2) (lam.prod σ) := hg.mul_prod hf
  have hI : Integrable (Function.uncurry fun x z => g x * (f z * k x z)) (lam.prod σ) := by
    have hm : AEStronglyMeasurable (fun u : N × X => (g u.1 * f u.2) * k u.1 u.2) (lam.prod σ) :=
      h0.aestronglyMeasurable.mul hk.aestronglyMeasurable
    refine (h0.mono (hm.congr (Eventually.of_forall fun u => ?_)) (Eventually.of_forall fun u => ?_))
    · simp [Function.uncurry, mul_assoc]
    · simp only [Function.uncurry, norm_mul]
      have := hk1 u.1 u.2
      have h2 := norm_nonneg (g u.1)
      have h3 := norm_nonneg (f u.2)
      nlinarith [mul_nonneg h2 h3]
  have e1 : ∀ x, g x * ∫ z, f z * k x z ∂σ = ∫ z, g x * (f z * k x z) ∂σ :=
    fun x => (integral_const_mul _ _).symm
  have e2 : ∀ z, f z * (∫ x, g x * k x z ∂lam) = ∫ x, g x * (f z * k x z) ∂lam := by
    intro z
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    ring
  simp_rw [e1, e2]
  exact integral_integral_swap hI

end Seq

theorem dens_seq {X N : Type} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] [MeasurableSpace N]
    (σ : Measure X) (lam : Measure N) [SFinite lam] (k : N → X → ℂ) (Y : Set X)
    (g : ℕ → N → ℂ) (G : ℕ → X → ℝ) (hσ : IsFiniteMeasureOnCompacts σ)
    (hk : Measurable (Function.uncurry k)) (hk1 : ∀ x z, ‖k x z‖ ≤ 1) (hY : IsClosed Y) (hσY : σ Yᶜ = 0)
    (hg : ∀ j, Integrable (g j) lam ∧ (∀ x, ‖g j x‖ ≤ 1) ∧
      ∀ z ∈ Y, 0 ≤ G j z ∧ ∫ x, g j x * k x z ∂lam = G j z)
    (hg1 : ∀ x, Tendsto (g · x) atTop (𝓝 1)) :
    ∃ m : ℕ → Measure X, (∀ j, IsFiniteMeasureOnCompacts (m j)) ∧ (∀ j, m j Yᶜ = 0) ∧
      (∀ j (f : X → ℂ), Integrable f σ → Integrable f (m j)) ∧
      (∀ j (f : X → ℝ), Integrable f σ → Integrable f (m j)) ∧
      (∀ f : X → ℂ, Integrable f σ → Integrable (fun x => ∫ z, f z * k x z ∂σ) lam →
        Tendsto (fun j => ∫ z, f z ∂m j) atTop (𝓝 (∫ x, ∫ z, f z * k x z ∂σ ∂lam))) ∧
      ∀ (C : Set X) (ε : ℝ) (j : ℕ), (∀ z ∈ C, z ∈ Y → G j z ≤ ε) → 0 ≤ ε → ∀ f : X → ℝ, Integrable f σ →
        (∀ z, 0 ≤ f z) → (∀ z ∈ Y, z ∉ C → f z = 0) → ∫ z, f z ∂m j ≤ ε * ∫ z, f z ∂σ := by
  haveI := hσ
  have hYae : ∀ᵐ z ∂σ, z ∈ Y := by
    rw [ae_iff]; exact hσY
  let H : ℕ → X → ℂ := fun j z => ∫ x, g j x * k x z ∂lam
  have hHm : ∀ j, Measurable (H j) := fun j => (H_sm (g j) (hg j).1 hk).measurable
  let r : ℕ → X → ℝ≥0∞ := fun j z => ENNReal.ofReal (H j z).re
  have hrm : ∀ j, Measurable (r j) := fun j =>
    (Complex.measurable_re.comp (hHm j)).ennreal_ofReal
  have hrlt : ∀ j, ∀ᵐ z ∂σ, r j z < ∞ := fun j => Eventually.of_forall fun z => ENNReal.ofReal_lt_top
  have hrY : ∀ j z, z ∈ Y → (r j z).toReal = G j z ∧ H j z = G j z := by
    intro j z hz
    obtain ⟨h0, h1⟩ := (hg j).2.2 z hz
    have h2 : H j z = G j z := h1
    refine ⟨?_, h2⟩
    simp only [r]
    rw [h2, Complex.ofReal_re, ENNReal.toReal_ofReal h0]
  let B : ℕ → ℝ≥0∞ := fun j => ENNReal.ofReal (∫ x, ‖g j x‖ ∂lam)
  have hle : ∀ j, σ.withDensity (r j) ≤ B j • σ := by
    intro j
    refine Measure.le_iff.2 fun s hs => ?_
    rw [withDensity_apply _ hs, Measure.smul_apply, smul_eq_mul, ← setLIntegral_const]
    refine lintegral_mono fun z => ENNReal.ofReal_le_ofReal ?_
    exact (Complex.re_le_norm _).trans (H_bd (g j) (hg j).1 hk1 z)
  have hBt : ∀ j, B j ≠ ∞ := fun j => ENNReal.ofReal_ne_top
  have hint : ∀ {E : Type} [NormedAddCommGroup E] (j : ℕ) (f : X → E), Integrable f σ →
      Integrable f (σ.withDensity (r j)) := fun j f hf =>
    (hf.smul_measure (hBt j)).mono_measure (hle j)
  have hconv : ∀ j (f : X → ℂ), ∫ z, f z ∂σ.withDensity (r j) = ∫ z, f z * H j z ∂σ := by
    intro j f
    rw [integral_withDensity_eq_integral_toReal_smul (hrm j) (hrlt j)]
    refine integral_congr_ae ?_
    filter_upwards [hYae] with z hz
    obtain ⟨h1, h2⟩ := hrY j z hz
    rw [h1, h2, Complex.real_smul, mul_comm]
  refine ⟨fun j => σ.withDensity (r j), fun j => ⟨fun K hK => ?_⟩, fun j => ?_, hint, hint, ?_, ?_⟩
  · refine ((hle j) K).trans_lt ?_
    simp only [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top (hBt j).lt_top hK.measure_lt_top
  · exact withDensity_absolutelyContinuous σ _ hσY
  · intro f hf hT
    have e : ∀ j, ∫ z, f z ∂σ.withDensity (r j) = ∫ x, g j x * ∫ z, f z * k x z ∂σ ∂lam := by
      intro j
      rw [hconv, fub σ (g j) f (hg j).1 hf hk hk1]
    simp_rw [e]
    refine tendsto_integral_of_dominated_convergence (fun x => ‖∫ z, f z * k x z ∂σ‖)
      (fun j => (hg j).1.aestronglyMeasurable.mul hT.aestronglyMeasurable) hT.norm
      (fun j => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) ((hg j).2.1 x)
    · simpa using (hg1 x).mul_const (∫ z, f z * k x z ∂σ)
  · intro C ε j hC hε f hf hf0 hfC
    rw [integral_withDensity_eq_integral_toReal_smul (hrm j) (hrlt j), ← integral_const_mul]
    refine integral_mono_of_nonneg (Eventually.of_forall fun z => ?_) (hf.const_mul ε) ?_
    · exact smul_nonneg ENNReal.toReal_nonneg (hf0 z)
    · filter_upwards [hYae] with z hz
      simp only [smul_eq_mul]
      by_cases hzC : z ∈ C
      · rw [(hrY j z hz).1]
        exact mul_le_mul_of_nonneg_right (hC z hzC hz) (hf0 z)
      · simp [hfC z hz hzC]

theorem re_tendsto {X : Type} [MeasurableSpace X] (m : ℕ → Measure X) (ν : Measure X) (f : X → ℝ)
    (hf : ∀ j, Integrable f (m j)) (hfν : Integrable f ν)
    (h : Tendsto (fun j => ∫ z, ((f z : ℝ) : ℂ) ∂m j) atTop (𝓝 (∫ z, ((f z : ℝ) : ℂ) ∂ν))) :
    Tendsto (fun j => ∫ z, f z ∂m j) atTop (𝓝 (∫ z, f z ∂ν)) := by
  have := (Complex.continuous_re.tendsto _).comp h
  simpa [Function.comp_def, integral_complex_ofReal] using this

section Tail
variable {X : Type} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]

theorem vague_all (σ ν : Measure X) [IsFiniteMeasureOnCompacts σ] [IsFiniteMeasureOnCompacts ν]
    (m : ℕ → Measure X) (A : Submodule ℂ (X → ℂ)) (hA : PositivityTheory.Rg.Rsw.Em.Rich A)
    (hmi : ∀ j (f : X → ℂ), Integrable f σ → Integrable f (m j))
    (hνA : ∀ f ∈ A, Tendsto (fun j => ∫ z, f z ∂m j) atTop (𝓝 (∫ z, f z ∂ν)))
    (f : X → ℂ) (hf : Continuous f) (hc : HasCompactSupport f) :
    Tendsto (fun j => ∫ z, f z ∂m j) atTop (𝓝 (∫ z, f z ∂ν)) := by
  obtain ⟨b, hbA, hb0, hb⟩ := sw_bump A hA f hf hc
  have hbc := hA.cc b hbA
  have hbσ : Integrable b σ := hbc.1.integrable_of_hasCompactSupport hbc.2
  have hbm : ∀ j, Integrable (fun z => (b z).re) (m j) := fun j => (hmi j b hbσ).re
  have hbν : Integrable b ν := hbc.1.integrable_of_hasCompactSupport hbc.2
  refine approx_tendsto m ν f (fun z => (b z).re) (∫ z, b z ∂ν).re
    (fun j => hmi j f (hf.integrable_of_hasCompactSupport hc))
    hbm ?_ (hf.integrable_of_hasCompactSupport hc) hbν.re ?_
  · have := (Complex.continuous_re.tendsto _).comp (hνA b hbA)
    refine this.congr fun j => ?_
    exact (integral_re (hmi j b hbσ)).symm
  · intro ε hε
    obtain ⟨h, hhA, hh⟩ := hb ε hε
    have hhc := hA.cc h hhA
    exact ⟨h, fun j => hmi j h (hhc.1.integrable_of_hasCompactSupport hhc.2),
      hhc.1.integrable_of_hasCompactSupport hhc.2, hνA h hhA, hh⟩

theorem vague_real (σ ν : Measure X) [IsFiniteMeasureOnCompacts σ] [IsFiniteMeasureOnCompacts ν]
    (m : ℕ → Measure X)
    (hmir : ∀ j (f : X → ℝ), Integrable f σ → Integrable f (m j))
    (hV : ∀ f : X → ℂ, Continuous f → HasCompactSupport f →
      Tendsto (fun j => ∫ z, f z ∂m j) atTop (𝓝 (∫ z, f z ∂ν)))
    (f : X → ℝ) (hf : Continuous f) (hc : HasCompactSupport f) :
    Tendsto (fun j => ∫ z, f z ∂m j) atTop (𝓝 (∫ z, f z ∂ν)) := by
  have hσf : Integrable f σ := hf.integrable_of_hasCompactSupport hc
  refine re_tendsto m ν f (fun j => hmir j f hσf) (hf.integrable_of_hasCompactSupport hc) ?_
  exact hV (fun z => ((f z : ℝ) : ℂ)) (Complex.continuous_ofReal.comp hf)
    (hc.comp_left Complex.ofReal_zero)

theorem nu_support (σ ν : Measure X) [IsFiniteMeasureOnCompacts σ] [IsFiniteMeasureOnCompacts ν]
    (m : ℕ → Measure X) (Y Z : Set X) (hY : IsClosed Y) (hZ : IsClosed Z) (G : ℕ → X → ℝ)
    (hmY : ∀ j, m j Yᶜ = 0)
    (hsmall : ∀ C : Set X, IsCompact C → C ⊆ Y → Disjoint C Z → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ j in atTop, ∀ z ∈ C, G j z ≤ ε)
    (hmsm : ∀ (C : Set X) (ε : ℝ) (j : ℕ), (∀ z ∈ C, z ∈ Y → G j z ≤ ε) → 0 ≤ ε → ∀ f : X → ℝ,
      Integrable f σ → (∀ z, 0 ≤ f z) → (∀ z ∈ Y, z ∉ C → f z = 0) →
      ∫ z, f z ∂m j ≤ ε * ∫ z, f z ∂σ)
    (hVr : ∀ f : X → ℝ, Continuous f → HasCompactSupport f →
      Tendsto (fun j => ∫ z, f z ∂m j) atTop (𝓝 (∫ z, f z ∂ν))) :
    ν (Y ∩ Z)ᶜ = 0 := by
  have hνY : ν Yᶜ = 0 := by
    refine null_of_test ν _ hY.isOpen_compl fun c hc hcs hc0 hcU => ?_
    refine tendsto_nhds_unique (hVr c hc hcs) ?_
    refine tendsto_const_nhds.congr fun j => ?_
    symm
    refine integral_eq_zero_of_ae ?_
    have h0 : ∀ᵐ z ∂m j, z ∈ Y := by
      rw [ae_iff]; exact hmY j
    filter_upwards [h0] with z hz
    by_contra hne
    exact hcU (subset_tsupport _ hne) hz
  have hνZ : ν Zᶜ = 0 := by
    refine null_of_test ν _ hZ.isOpen_compl fun c hc hcs hc0 hcU => ?_
    have hσc : Integrable c σ := hc.integrable_of_hasCompactSupport hcs
    set I := ∫ z, c z ∂σ with hI
    have hI0 : 0 ≤ I := integral_nonneg hc0
    have hν0 : 0 ≤ ∫ z, c z ∂ν := integral_nonneg hc0
    have hC : IsCompact (tsupport c ∩ Y) := hcs.isCompact.inter_right hY
    have hle : ∀ ε : ℝ, 0 < ε → ∫ z, c z ∂ν ≤ ε * I := by
      intro ε hε
      have hev := hsmall _ hC Set.inter_subset_right
        (Set.disjoint_left.2 fun z hz hzZ => hcU hz.1 hzZ) ε hε
      refine le_of_tendsto (hVr c hc hcs) ?_
      filter_upwards [hev] with j hj
      refine hmsm (tsupport c ∩ Y) ε j (fun z hz _ => hj z hz) hε.le c hσc hc0 ?_
      intro z hzY hzC
      by_contra hne
      exact hzC ⟨subset_tsupport _ hne, hzY⟩
    refine le_antisymm ?_ hν0
    by_contra hpos
    push_neg at hpos
    set a := ∫ z, c z ∂ν with ha
    have hε : 0 < a / (2 * (I + 1)) := by positivity
    have h1 := hle _ hε
    have h2 : a / (2 * (I + 1)) * I ≤ a / 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_nonneg hpos.le hI0]
    linarith
  rw [Set.compl_inter]
  exact measure_union_null hνY hνZ

theorem nu_formula (σ ν : Measure X) [IsFiniteMeasureOnCompacts σ] [IsFiniteMeasureOnCompacts ν]
    (m : ℕ → Measure X)
    (hmi : ∀ j (f : X → ℂ), Integrable f σ → Integrable f (m j))
    (hV : ∀ f : X → ℂ, Continuous f → HasCompactSupport f →
      Tendsto (fun j => ∫ z, f z ∂m j) atTop (𝓝 (∫ z, f z ∂ν)))
    (hVr : ∀ f : X → ℝ, Continuous f → HasCompactSupport f →
      Tendsto (fun j => ∫ z, f z ∂m j) atTop (𝓝 (∫ z, f z ∂ν)))
    (hmir : ∀ j (f : X → ℝ), Integrable f σ → Integrable f (m j))
    (f f₀ : X → ℂ) (l l₀ : ℂ) (hf : Continuous f) (hf₀ : Continuous f₀)
    (hn : ∀ z, 0 ≤ (f₀ z).re ∧ (f₀ z).im = 0) (hfi : Integrable f σ) (hf₀i : Integrable f₀ σ)
    (hl : Tendsto (fun j => ∫ z, f z ∂m j) atTop (𝓝 l))
    (hl₀ : Tendsto (fun j => ∫ z, f₀ z ∂m j) atTop (𝓝 l₀))
    (happ : ∀ ε : ℝ, 0 < ε → ∃ f₁ : X → ℂ, Continuous f₁ ∧ HasCompactSupport f₁ ∧
      ∀ z, ‖f z - f₁ z‖ ≤ ε * (f₀ z).re) : l = ∫ z, f z ∂ν := by
  have hbc : Continuous fun z => (f₀ z).re := Complex.continuous_re.comp hf₀
  have hbm : ∀ j, Integrable (fun z => (f₀ z).re) (m j) := fun j => (hmi j f₀ hf₀i).re
  have hb : Tendsto (fun j => ∫ z, (f₀ z).re ∂m j) atTop (𝓝 l₀.re) := by
    refine ((Complex.continuous_re.tendsto _).comp hl₀).congr fun j => ?_
    exact (integral_re (hmi j f₀ hf₀i)).symm
  have hminor : ∫⁻ z, ENNReal.ofReal (f₀ z).re ∂ν ≤ ENNReal.ofReal l₀.re := by
    refine lintegral_le_of_minor ν _ hbc (fun z => (hn z).1) _ fun c hc hcs hc0 hcb => ?_
    refine le_of_tendsto_of_tendsto' (hVr c hc hcs) hb fun j => ?_
    exact integral_mono (hmir j c (hc.integrable_of_hasCompactSupport hcs)) (hbm j) hcb
  have hbν : Integrable (fun z => (f₀ z).re) ν := by
    refine ⟨hbc.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun z => (hn z).1)]
    exact hminor.trans_lt ENNReal.ofReal_lt_top
  have hfν : Integrable f ν := by
    obtain ⟨f₁, h1, h2, h3⟩ := happ 1 one_pos
    have hf₁ : Integrable f₁ ν := h1.integrable_of_hasCompactSupport h2
    refine (hf₁.norm.add hbν).mono' hf.aestronglyMeasurable (Eventually.of_forall fun z => ?_)
    have h4 := h3 z
    have h5 : ‖f z‖ ≤ ‖f₁ z‖ + ‖f z - f₁ z‖ := by
      simpa using norm_add_le (f₁ z) (f z - f₁ z)
    simp only [Pi.add_apply]
    linarith
  have := approx_tendsto m ν f (fun z => (f₀ z).re) l₀.re (fun j => hmi j f hfi) hbm hb hfν hbν ?_
  · exact tendsto_nhds_unique hl this
  · intro ε hε
    obtain ⟨f₁, h1, h2, h3⟩ := happ ε hε
    exact ⟨f₁, fun j => hmi j f₁ (h1.integrable_of_hasCompactSupport h2),
      h1.integrable_of_hasCompactSupport h2, hV f₁ h1 h2, h3⟩

end Tail

theorem dens_main (hP : PositivityTheory.Rg.Rsw.L.PosExt) : PositivityTheory.Rg.Rsw.Em.Dens := by
  intro X N _ _ _ _ _ _ _ σ lam _ k A Z Y g G hσ hk hk1 hA hZ hY hσY hg hg1 hsmall hT
  obtain ⟨m, hmc, hmY, hmi, hmir, hlim, hmsm⟩ := dens_seq σ lam k Y g G hσ hk hk1 hY hσY hg hg1
  have hAi : ∀ f ∈ A, Integrable f σ := fun f hf =>
    (hA.cc f hf).1.integrable_of_hasCompactSupport (hA.cc f hf).2
  have hlimA : ∀ f ∈ A, Tendsto (fun j => ∫ z, f z ∂m j) atTop (𝓝 (∫ x, ∫ z, f z * k x z ∂σ ∂lam)) :=
    fun f hf => hlim f (hAi f hf) (hT f hf)
  let L : A →ₗ[ℂ] ℂ :=
    { toFun := fun f => ∫ x, ∫ z, f.1 z * k x z ∂σ ∂lam
      map_add' := by
        intro f f'
        refine tendsto_nhds_unique (hlimA _ (f + f').2) ?_
        refine ((hlimA _ f.2).add (hlimA _ f'.2)).congr (fun j => ?_)
        rw [← integral_add (hmi j _ (hAi _ f.2)) (hmi j _ (hAi _ f'.2))]
        rfl
      map_smul' := by
        intro c f
        refine tendsto_nhds_unique (hlimA _ (c • f).2) ?_
        refine ((hlimA _ f.2).const_mul c).congr (fun j => ?_)
        simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [integral_const_mul] }
  have hLpos : ∀ f : A, (∀ x, 0 ≤ (f.1 x).re ∧ (f.1 x).im = 0) → 0 ≤ (L f).re ∧ (L f).im = 0 := by
    intro f hf
    have hre : ∀ j, ∫ z, f.1 z ∂m j = ((∫ z, (f.1 z).re ∂m j : ℝ) : ℂ) := by
      intro j
      rw [← integral_complex_ofReal]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      apply Complex.ext <;> simp [(hf z).2]
    have hnn : ∀ j, 0 ≤ (∫ z, f.1 z ∂m j).re ∧ (∫ z, f.1 z ∂m j).im = 0 := by
      intro j
      rw [hre j]
      simp only [Complex.ofReal_re, Complex.ofReal_im, and_true]
      exact integral_nonneg fun z => (hf z).1
    have hl := hlimA _ f.2
    refine ⟨ge_of_tendsto' ((Complex.continuous_re.tendsto _).comp hl) fun j => (hnn j).1, ?_⟩
    exact tendsto_nhds_unique ((Complex.continuous_im.tendsto _).comp hl)
      (tendsto_const_nhds.congr fun j => (hnn j).2.symm)
  obtain ⟨hex, huniq⟩ := hP X A hA.cc hA.mul hA.star hA.sep hA.bump
  obtain ⟨ν, hνc, hν⟩ := hex L hLpos
  have hνL : ∀ f (hf : f ∈ A), ∫ x, ∫ z, f z * k x z ∂σ ∂lam = ∫ z, f z ∂ν := fun f hf => hν ⟨f, hf⟩
  have hνA : ∀ f ∈ A, Tendsto (fun j => ∫ z, f z ∂m j) atTop (𝓝 (∫ z, f z ∂ν)) := by
    intro f hf
    rw [← hνL f hf]
    exact hlimA f hf
  have hV := vague_all σ ν m A hA hmi hνA
  have hVr := vague_real σ ν m hmir hV
  refine ⟨ν, hνc, nu_support σ ν m Y Z hY hZ G hmY hsmall hmsm hVr, ?_, ?_⟩
  · intro f f₀ hf hf₀ hn hfi hf₀i hTf hTf₀ happ
    exact nu_formula σ ν m hmi hV hVr hmir f f₀ _ _ hf hf₀ hn hfi hf₀i (hlim f hfi hTf)
      (hlim f₀ hf₀i hTf₀) happ
  · intro Θ κ hΘ
    have hmap : IsFiniteMeasureOnCompacts (ν.map Θ) := by
      refine ⟨fun K hK => ?_⟩
      rw [Θ.measurableEmbedding.map_apply]
      have : Θ ⁻¹' K = Θ.symm '' K := (Θ.symm.image_eq_preimage_symm K).symm
      rw [this]
      exact (hK.image Θ.symm.continuous).measure_lt_top
    have hsm : IsFiniteMeasureOnCompacts (κ • ν) := by
      refine ⟨fun K hK => ?_⟩
      simp only [Measure.smul_apply]
      exact ENNReal.mul_lt_top ENNReal.coe_lt_top hK.measure_lt_top
    refine huniq _ _ hmap hsm fun f hf => ?_
    obtain ⟨h1, h2⟩ := hΘ f hf
    rw [Θ.measurableEmbedding.integral_map, integral_smul_nnreal_measure]
    have h3 := hνL _ h1
    simp only [Function.comp_apply] at h3
    rw [← h3, h2, hνL f hf]
    rfl

end GlobalTheory.CompanionTheory.EisDens
