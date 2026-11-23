import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSplitK
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WhitFree.AvgInf.Lim

open Filter Topology

section Gen

variable {V H Z : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
  [TopologicalSpace H] [MeasurableSpace H] [BorelSpace H]
  {μ : Measure V} {ν : Measure H} {f : V → Z} {ι : H → Z} {q : V → H} {U : Set V} {m : H → Measure V}

theorem ae_fibre (hι : Function.Injective ι) (hf : ∀ X, ι (q X) = f X)
    (h : IsFibreFamily μ f ι U ν Set.univ m) (b : H) : ∀ᵐ X ∂(m b), q X = b ∧ X ∈ U := by
  have h1 : f ⁻¹' {ι b} ∩ U ∈ ae (m b) := mem_ae_iff.2 (h.1 b)
  filter_upwards [h1] with X hX
  exact ⟨hι ((hf X).trans hX.1), hX.2⟩

theorem lintegral_mul_base (hι : Function.Injective ι) (hf : ∀ X, ι (q X) = f X)
    (h : IsFibreFamily μ f ι U ν Set.univ m) (hq : Measurable q) {g : V → ℝ≥0∞} (hg : Measurable g)
    {s : H → ℝ≥0∞} (hs : Measurable s) :
    ∫⁻ X in U, g X * s (q X) ∂μ = ∫⁻ b, s b * ∫⁻ X, g X ∂(m b) ∂ν := by
  rw [h.2.1 (fun X => g X * s (q X)) (hg.mul (hs.comp hq))]
  refine lintegral_congr fun b => ?_
  have h1 : ∫⁻ X, g X * s (q X) ∂(m b) = ∫⁻ X, g X * s b ∂(m b) := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_fibre hι hf h b] with X hX
    rw [hX.1]
  rw [h1, lintegral_mul_const _ hg, mul_comm]

theorem tail_lintegral {φ : V → ℂ} (hφ : Measurable φ) (hq : Measurable q) {A : Set V}
    (hA : MeasurableSet A) {e : ℝ≥0∞}
    (hY : ∀ Y, MeasurableSet Y → ∫⁻ X in Aᶜ ∩ q ⁻¹' Y, ‖φ X‖ₑ ∂μ ≤ e * ν Y)
    {s : H → ℝ≥0∞} (hs : Measurable s) :
    ∫⁻ X in Aᶜ, ‖φ X‖ₑ * s (q X) ∂μ ≤ e * ∫⁻ y, s y ∂ν := by
  have hφe : Measurable fun X => ‖φ X‖ₑ := hφ.enorm
  set ρ : Measure V := (μ.restrict Aᶜ).withDensity fun X => ‖φ X‖ₑ with hρ
  have hle : ρ.map q ≤ e • ν := by
    refine Measure.le_iff.2 fun Y hYm => ?_
    rw [Measure.map_apply hq hYm, hρ, withDensity_apply _ (hq hYm),
      Measure.restrict_restrict (hq hYm), Set.inter_comm, Measure.smul_apply, smul_eq_mul]
    exact hY Y hYm
  calc ∫⁻ X in Aᶜ, ‖φ X‖ₑ * s (q X) ∂μ = ∫⁻ X, s (q X) ∂ρ := by
        rw [hρ]
        exact (lintegral_withDensity_eq_lintegral_mul _ hφe (hs.comp hq)).symm
    _ = ∫⁻ y, s y ∂(ρ.map q) := (lintegral_map hs hq).symm
    _ ≤ ∫⁻ y, s y ∂(e • ν) := lintegral_mono' hle le_rfl
    _ = e * ∫⁻ y, s y ∂ν := by rw [lintegral_smul_measure, smul_eq_mul]

end Gen

section Cut

variable {V : Type} [TopologicalSpace V] [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V]

theorem exists_cutoffs {U : Set V} (hU : IsOpen U) :
    ∃ χ : ℕ → V → ℝ, (∀ n, Continuous (χ n) ∧ HasCompactSupport (χ n) ∧ tsupport (χ n) ⊆ U ∧
      ∀ X, 0 ≤ χ n X ∧ χ n X ≤ 1) ∧ ∀ X ∈ U, ∀ᶠ n in atTop, χ n X = 1 := by
  haveI : LocallyCompactSpace U := hU.isOpenEmbedding_subtypeVal.locallyCompactSpace
  have hK : ∀ n, IsCompact (Subtype.val '' compactCovering U n) := fun n =>
    (isCompact_compactCovering U n).image continuous_subtype_val
  have hKU : ∀ n, Subtype.val '' compactCovering U n ⊆ U := by
    rintro n _ ⟨x, -, rfl⟩
    exact x.2
  choose χ h1 h2 h3 h4 using fun n =>
    exists_continuousMap_one_of_isCompact_subset_isOpen (hK n) hU (hKU n)
  refine ⟨fun n => χ n, fun n => ⟨(χ n).continuous, h2 n, h3 n, fun X => h4 n X⟩, fun X hX => ?_⟩
  obtain ⟨n0, hn0⟩ := exists_mem_compactCovering (⟨X, hX⟩ : U)
  filter_upwards [eventually_ge_atTop n0] with n hn
  exact h1 n ⟨⟨X, hX⟩, compactCovering_subset U hn hn0, rfl⟩

end Cut

section SlopeTestRemainingChoices

theorem integrable_mul_bdd' {α 𝕜 : Type} [MeasurableSpace α] [NormedRing 𝕜] {ρ : Measure α} {a b : α → 𝕜}
    (ha : Integrable a ρ) (hb : AEStronglyMeasurable b ρ) {C : ℝ} (hC : ∀ x, ‖b x‖ ≤ C) :
    Integrable (fun x => a x * b x) ρ :=
  (ha.norm.mul_const C).mono' (ha.aestronglyMeasurable.mul hb) (ae_of_all _ fun x =>
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _)))

theorem integral_re_im {α : Type} [MeasurableSpace α] {ρ : Measure α} {a b : α → ℝ}
    (ha : Integrable a ρ) (hb : Integrable b ρ) :
    ∫ x, ((a x : ℂ) + (b x : ℂ) * Complex.I) ∂ρ =
      ((∫ x, a x ∂ρ : ℝ) : ℂ) + ((∫ x, b x ∂ρ : ℝ) : ℂ) * Complex.I := by
  rw [integral_add ha.ofReal (hb.ofReal.mul_const _), integral_mul_const, integral_complex_ofReal,
    integral_complex_ofReal]

theorem enorm_coe (x : ℝ) : ‖(x : ℂ)‖ₑ = ‖x‖ₑ := by
  rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, Complex.norm_real]

end SlopeTestRemainingChoices

section Fib

variable {V H Z : Type} [TopologicalSpace V] [T2Space V] [LocallyCompactSpace V]
  [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
  [TopologicalSpace H] [T2Space H] [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H]
  {μ : Measure V} {ν : Measure H} {f : V → Z} {ι : H → Z} {q : V → H} {U : Set V} {m : H → Measure V}

theorem fibre_le [ν.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts ν]
    (hι : Function.Injective ι) (hf : ∀ X, ι (q X) = f X)
    (h : IsFibreFamily μ f ι U ν Set.univ m) (hq : Measurable q) {φ : V → ℂ} {A : Set V}
    (hA : MeasurableSet A) {e : ℝ≥0∞}
    (hY : ∀ Y, MeasurableSet Y → ∫⁻ X in Aᶜ ∩ q ⁻¹' Y, ‖φ X‖ₑ ∂μ ≤ e * ν Y)
    {g : V → ℝ} (hgc : Continuous g) (hgs : HasCompactSupport g) (hgU : tsupport g ⊆ U)
    (hg0 : ∀ X, 0 ≤ g X) (hgA : ∀ X ∈ A, g X = 0) (hgφ : ∀ X, g X ≤ ‖φ X‖) (c : H) :
    ∫⁻ X, ENNReal.ofReal (g X) ∂(m c) ≤ e := by
  obtain ⟨hint, hcont⟩ := h.2.2 g hgc hgs hgU
  set G : H → ℝ := fun b => ∫ X, g X ∂(m b) with hGdef
  have hG : Continuous G := continuousOn_univ.1 hcont
  have hlin : ∀ b, ∫⁻ X, ENNReal.ofReal (g X) ∂(m b) = ENNReal.ofReal (G b) := fun b =>
    (ofReal_integral_eq_lintegral_ofReal (hint b trivial) (Eventually.of_forall hg0)).symm
  rw [hlin c]
  by_contra hlt
  push_neg at hlt
  obtain ⟨e', he1, he2⟩ := exists_between hlt
  have hO : IsOpen {b | e' < ENNReal.ofReal (G b)} :=
    isOpen_lt continuous_const (ENNReal.continuous_ofReal.comp hG)
  obtain ⟨K, hK, hcK, hKO⟩ := exists_compact_subset hO he2
  have hYo : IsOpen (interior K) := isOpen_interior
  have hYm : MeasurableSet (interior K) := hYo.measurableSet
  have hpos : ν (interior K) ≠ 0 := (hYo.measure_pos ν ⟨c, hcK⟩).ne'
  have hfin : ν (interior K) ≠ ⊤ :=
    ((measure_mono interior_subset).trans_lt hK.measure_lt_top).ne
  have key : ∫⁻ b in interior K, ENNReal.ofReal (G b) ∂ν ≤ e * ν (interior K) := by
    calc ∫⁻ b in interior K, ENNReal.ofReal (G b) ∂ν
        = ∫⁻ b, (interior K).indicator 1 b * ∫⁻ X, ENNReal.ofReal (g X) ∂(m b) ∂ν := by
          rw [← lintegral_indicator hYm]
          refine lintegral_congr fun b => ?_
          by_cases hb : b ∈ interior K <;> simp [hb, hlin]
      _ = ∫⁻ X in U, ENNReal.ofReal (g X) * (interior K).indicator 1 (q X) ∂μ :=
          (lintegral_mul_base hι hf h hq hgc.measurable.ennreal_ofReal
            (measurable_one.indicator hYm)).symm
      _ ≤ ∫⁻ X, ENNReal.ofReal (g X) * (interior K).indicator 1 (q X) ∂μ :=
          setLIntegral_le_lintegral _ _
      _ ≤ ∫⁻ X, (Aᶜ ∩ q ⁻¹' interior K).indicator (fun X => ‖φ X‖ₑ) X ∂μ := by
          refine lintegral_mono fun X => ?_
          by_cases hXA : X ∈ A
          · simp [hgA X hXA]
          by_cases hXY : q X ∈ interior K
          · have hmem : X ∈ Aᶜ ∩ q ⁻¹' interior K := ⟨hXA, hXY⟩
            rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hXY, Pi.one_apply, mul_one,
              ← ofReal_norm_eq_enorm]
            exact ENNReal.ofReal_le_ofReal (hgφ X)
          · simp [hXY]
      _ = ∫⁻ X in Aᶜ ∩ q ⁻¹' interior K, ‖φ X‖ₑ ∂μ := lintegral_indicator (hA.compl.inter (hq hYm)) _
      _ ≤ e * ν (interior K) := hY _ hYm
  have low : e' * ν (interior K) ≤ ∫⁻ b in interior K, ENNReal.ofReal (G b) ∂ν := by
    rw [← setLIntegral_const]
    exact setLIntegral_mono' hYm fun b hb => (hKO (interior_subset hb)).le
  have hfinal : e' * ν (interior K) ≤ e * ν (interior K) := low.trans key
  have : e' ≤ e := by
    first
      | exact (ENNReal.mul_le_mul_iff_left hpos hfin).1 hfinal
      | exact (ENNReal.mul_le_mul_right hpos hfin).1 hfinal
  exact absurd he1 (not_lt.2 this)

theorem fibre_tail [ν.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts ν] (hU : IsOpen U)
    (hι : Function.Injective ι) (hf : ∀ X, ι (q X) = f X)
    (h : IsFibreFamily μ f ι U ν Set.univ m) (hq : Measurable q) {φ : V → ℂ} (hφ : Continuous φ)
    {A : Set V} (hA : MeasurableSet A) {e : ℝ≥0∞}
    (hY : ∀ Y, MeasurableSet Y → ∫⁻ X in Aᶜ ∩ q ⁻¹' Y, ‖φ X‖ₑ ∂μ ≤ e * ν Y)
    {χ : V → ℝ} (hχ : Continuous χ) (hχ01 : ∀ X, 0 ≤ χ X ∧ χ X ≤ 1) (hχA : ∀ X ∈ A, χ X = 1) (c : H) :
    ∫⁻ X, ‖φ X‖ₑ * ENNReal.ofReal (1 - χ X) ∂(m c) ≤ e := by
  obtain ⟨ψ, hψ, hev⟩ := exists_cutoffs hU
  set g : ℕ → V → ℝ := fun n X => ‖φ X‖ * (1 - χ X) * ψ n X with hg
  have hgc : ∀ n, Continuous (g n) := fun n =>
    (hφ.norm.mul (continuous_const.sub hχ)).mul (hψ n).1
  have hgsub : ∀ n, Function.support (g n) ⊆ Function.support (ψ n) := fun n X hX h0 =>
    hX (by simp [hg, show ψ n X = 0 from h0])
  have hle : ∀ n, ∫⁻ X, ENNReal.ofReal (g n X) ∂(m c) ≤ e := fun n =>
    fibre_le hι hf h hq hA hY (hgc n) ((hψ n).2.1.mono (hgsub n))
      ((closure_mono (hgsub n)).trans (hψ n).2.2.1)
      (fun X => mul_nonneg (mul_nonneg (norm_nonneg _) (sub_nonneg.2 (hχ01 X).2)) ((hψ n).2.2.2 X).1)
      (fun X hX => by simp [hg, hχA X hX])
      (fun X => by
        have h1 : 1 - χ X ≤ 1 := by linarith [(hχ01 X).1]
        have h2 : 0 ≤ 1 - χ X := sub_nonneg.2 (hχ01 X).2
        have h3 := (hψ n).2.2.2 X
        have h4 : (1 - χ X) * ψ n X ≤ 1 := mul_le_one₀ h1 h3.1 h3.2
        calc g n X = ‖φ X‖ * ((1 - χ X) * ψ n X) := by simp only [hg]; ring
          _ ≤ ‖φ X‖ * 1 := mul_le_mul_of_nonneg_left h4 (norm_nonneg _)
          _ = ‖φ X‖ := mul_one _) c
  have hlim : ∀ᵐ X ∂(m c), ‖φ X‖ₑ * ENNReal.ofReal (1 - χ X) =
      liminf (fun n => ENNReal.ofReal (g n X)) atTop := by
    filter_upwards [ae_fibre hι hf h c] with X hX
    refine (Tendsto.liminf_eq (tendsto_const_nhds.congr' ?_)).symm
    filter_upwards [hev X hX.2] with n hn
    simp only [hg, hn, mul_one]
    rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm_eq_enorm]
  calc ∫⁻ X, ‖φ X‖ₑ * ENNReal.ofReal (1 - χ X) ∂(m c)
      = ∫⁻ X, liminf (fun n => ENNReal.ofReal (g n X)) atTop ∂(m c) := lintegral_congr_ae hlim
    _ ≤ liminf (fun n => ∫⁻ X, ENNReal.ofReal (g n X) ∂(m c)) atTop :=
        lintegral_liminf_le fun n => (hgc n).measurable.ennreal_ofReal
    _ ≤ liminf (fun _ : ℕ => e) atTop := liminf_le_liminf (Eventually.of_forall hle)
    _ = e := liminf_const e

theorem fibre_cut {φ : V → ℂ} (hφ : Continuous φ) (h : IsFibreFamily μ f ι U ν Set.univ m)
    {χ : V → ℝ} (hχ : Continuous χ) (hχs : HasCompactSupport χ) (hχU : tsupport χ ⊆ U) :
    (∀ b, Integrable (fun X => φ X * (χ X : ℂ)) (m b)) ∧
      Continuous fun b => ∫ X, φ X * (χ X : ℂ) ∂(m b) := by
  have hsup : ∀ a : V → ℝ, Function.support (fun X => a X * χ X) ⊆ Function.support χ :=
    fun a X hX h0 => hX (by simp [show χ X = 0 from h0])
  have hp : ∀ a : V → ℝ, Continuous a → (∀ b, Integrable (fun X => a X * χ X) (m b)) ∧
      Continuous fun b => ∫ X, a X * χ X ∂(m b) := fun a ha => by
    obtain ⟨h1, h2⟩ := h.2.2 (fun X => a X * χ X) (ha.mul hχ) (hχs.mono (hsup a))
      ((closure_mono (hsup a)).trans hχU)
    exact ⟨fun b => h1 b trivial, continuousOn_univ.1 h2⟩
  obtain ⟨i1, c1⟩ := hp (fun X => (φ X).re) (Complex.continuous_re.comp hφ)
  obtain ⟨i2, c2⟩ := hp (fun X => (φ X).im) (Complex.continuous_im.comp hφ)
  have hid : ∀ X, φ X * (χ X : ℂ) =
      (((φ X).re * χ X : ℝ) : ℂ) + (((φ X).im * χ X : ℝ) : ℂ) * Complex.I := fun X => by
    apply Complex.ext <;> simp
  simp_rw [hid]
  refine ⟨fun b => (i1 b).ofReal.add ((i2 b).ofReal.mul_const _), ?_⟩
  simp_rw [integral_re_im (i1 _) (i2 _)]
  exact (Complex.continuous_ofReal.comp c1).add
    ((Complex.continuous_ofReal.comp c2).mul continuous_const)

theorem fibre_integrable {φ : V → ℂ} (hφ : Continuous φ) (h : IsFibreFamily μ f ι U ν Set.univ m)
    {χ : V → ℝ} (hχ : Continuous χ) (hχs : HasCompactSupport χ) (hχU : tsupport χ ⊆ U)
    (hχ01 : ∀ X, 0 ≤ χ X ∧ χ X ≤ 1) {c : H}
    (ht : ∫⁻ X, ‖φ X‖ₑ * ENNReal.ofReal (1 - χ X) ∂(m c) < ⊤) : Integrable φ (m c) := by
  refine ⟨hφ.aestronglyMeasurable, ?_⟩
  have h1 := ((fibre_cut hφ h hχ hχs hχU).1 c).2
  have hm1 : Measurable fun X => ‖φ X‖ₑ * ENNReal.ofReal (1 - χ X) :=
    hφ.measurable.enorm.mul (continuous_const.sub hχ).measurable.ennreal_ofReal
  have hle : ∀ X, ‖φ X‖ₑ ≤ ‖φ X * (χ X : ℂ)‖ₑ + ‖φ X‖ₑ * ENNReal.ofReal (1 - χ X) := fun X => by
    rw [enorm_mul, enorm_coe, ← mul_add]
    have : (1 : ℝ≥0∞) ≤ ‖χ X‖ₑ + ENNReal.ofReal (1 - χ X) := by
      rw [← ofReal_norm_eq_enorm, Real.norm_of_nonneg (hχ01 X).1,
        ← ENNReal.ofReal_add (hχ01 X).1 (sub_nonneg.2 (hχ01 X).2)]
      simp
    calc ‖φ X‖ₑ = ‖φ X‖ₑ * 1 := (mul_one _).symm
      _ ≤ _ := by gcongr
  calc ∫⁻ X, ‖φ X‖ₑ ∂(m c)
      ≤ ∫⁻ X, (‖φ X * (χ X : ℂ)‖ₑ + ‖φ X‖ₑ * ENNReal.ofReal (1 - χ X)) ∂(m c) := lintegral_mono hle
    _ = ∫⁻ X, ‖φ X * (χ X : ℂ)‖ₑ ∂(m c) + ∫⁻ X, ‖φ X‖ₑ * ENNReal.ofReal (1 - χ X) ∂(m c) :=
        lintegral_add_right _ hm1
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨h1, ht⟩

theorem fibre_diff {φ : V → ℂ} {χ : V → ℝ} {c : H} (h1 : Integrable φ (m c))
    (h2 : Integrable (fun X => φ X * (χ X : ℂ)) (m c)) (hχ01 : ∀ X, 0 ≤ χ X ∧ χ X ≤ 1) {ε : ℝ}
    (hε : 0 ≤ ε) (ht : ∫⁻ X, ‖φ X‖ₑ * ENNReal.ofReal (1 - χ X) ∂(m c) ≤ ENNReal.ofReal ε) :
    ‖∫ X, φ X ∂(m c) - ∫ X, φ X * (χ X : ℂ) ∂(m c)‖ ≤ ε := by
  rw [← integral_sub h1 h2]
  have h3 : ‖∫ X, (φ X - φ X * (χ X : ℂ)) ∂(m c)‖ₑ ≤ ENNReal.ofReal ε := by
    refine (enorm_integral_le_lintegral_enorm _).trans (le_trans (le_of_eq ?_) ht)
    refine lintegral_congr fun X => ?_
    have : φ X - φ X * (χ X : ℂ) = φ X * ((1 - χ X : ℝ) : ℂ) := by push_cast; ring
    rw [this, enorm_mul, enorm_coe, ← ofReal_norm_eq_enorm (1 - χ X),
      Real.norm_of_nonneg (sub_nonneg.2 (hχ01 X).2)]
  rw [← ofReal_norm_eq_enorm] at h3
  exact (ENNReal.ofReal_le_ofReal_iff hε).1 h3

theorem pos_identity (hUm : MeasurableSet U) (hι : Function.Injective ι) (hf : ∀ X, ι (q X) = f X)
    (h : IsFibreFamily μ f ι U ν Set.univ m) (hq : Continuous q)
    {g : V → ℝ} (hgc : Continuous g) (hgs : HasCompactSupport g) (hgU : tsupport g ⊆ U)
    (hg0 : ∀ X, 0 ≤ g X) {s : H → ℝ} (hsc : Continuous s) (hs0 : ∀ y, 0 ≤ s y) :
    ∫ X, g X * s (q X) ∂μ = ∫ b, s b * ∫ X, g X ∂(m b) ∂ν := by
  obtain ⟨hint, hcont⟩ := h.2.2 g hgc hgs hgU
  have hG : Continuous fun b => ∫ X, g X ∂(m b) := continuousOn_univ.1 hcont
  have hG0 : ∀ b, 0 ≤ ∫ X, g X ∂(m b) := fun b => integral_nonneg hg0
  have hlin : ∀ b, ∫⁻ X, ENNReal.ofReal (g X) ∂(m b) = ENNReal.ofReal (∫ X, g X ∂(m b)) := fun b =>
    (ofReal_integral_eq_lintegral_ofReal (hint b trivial) (Eventually.of_forall hg0)).symm
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun X => mul_nonneg (hg0 X) (hs0 _))
      (hgc.mul (hsc.comp hq)).aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun b => mul_nonneg (hs0 b) (hG0 b))
      (hsc.mul hG).aestronglyMeasurable]
  congr 1
  calc ∫⁻ X, ENNReal.ofReal (g X * s (q X)) ∂μ
      = ∫⁻ X in U, ENNReal.ofReal (g X) * ENNReal.ofReal (s (q X)) ∂μ := by
        rw [← lintegral_indicator hUm]
        refine lintegral_congr fun X => ?_
        by_cases hX : X ∈ U
        · rw [Set.indicator_of_mem hX, ENNReal.ofReal_mul (hg0 X)]
        · rw [Set.indicator_of_notMem hX,
            image_eq_zero_of_notMem_tsupport (fun hh => hX (hgU hh))]
          simp
    _ = ∫⁻ b, ENNReal.ofReal (s b) * ∫⁻ X, ENNReal.ofReal (g X) ∂(m b) ∂ν :=
        lintegral_mul_base hι hf h hq.measurable hgc.measurable.ennreal_ofReal
          hsc.measurable.ennreal_ofReal
    _ = ∫⁻ b, ENNReal.ofReal (s b * ∫ X, g X ∂(m b)) ∂ν :=
        lintegral_congr fun b => by rw [hlin, ENNReal.ofReal_mul (hs0 b)]

theorem real_identity [IsFiniteMeasureOnCompacts ν] (hUm : MeasurableSet U)
    (hι : Function.Injective ι) (hf : ∀ X, ι (q X) = f X)
    (h : IsFibreFamily μ f ι U ν Set.univ m) (hq : Continuous q)
    {g : V → ℝ} (hgc : Continuous g) (hgs : HasCompactSupport g) (hgU : tsupport g ⊆ U)
    (hgμ : Integrable g μ) {s : H → ℝ} (hsc : Continuous s) (hss : HasCompactSupport s)
    (hs0 : ∀ y, 0 ≤ s y) :
    ∫ X, g X * s (q X) ∂μ = ∫ b, s b * ∫ X, g X ∂(m b) ∂ν := by
  obtain ⟨C, hC⟩ := hss.exists_bound_of_continuous hsc
  have hsm : AEStronglyMeasurable (fun X => s (q X)) μ := (hsc.comp hq).aestronglyMeasurable
  have hPsup : Function.support (fun X => max (g X) 0) ⊆ Function.support g := fun X hX h0 =>
    hX (by simp [show g X = 0 from h0])
  have hNsup : Function.support (fun X => max (-g X) 0) ⊆ Function.support g := fun X hX h0 =>
    hX (by simp [show g X = 0 from h0])
  have hPc : Continuous fun X => max (g X) 0 := hgc.max continuous_const
  have hNc : Continuous fun X => max (-g X) 0 := hgc.neg.max continuous_const
  have hPs := hgs.mono hPsup
  have hNs := hgs.mono hNsup
  have hPU := (closure_mono hPsup).trans hgU
  have hNU := (closure_mono hNsup).trans hgU
  have hP := pos_identity hUm hι hf h hq hPc hPs hPU (fun X => le_max_right _ _) hsc hs0
  have hN := pos_identity hUm hι hf h hq hNc hNs hNU (fun X => le_max_right _ _) hsc hs0
  have iP : Integrable (fun X => max (g X) 0 * s (q X)) μ :=
    integrable_mul_bdd' hgμ.pos_part hsm fun X => hC _
  have iN : Integrable (fun X => max (-g X) 0 * s (q X)) μ :=
    integrable_mul_bdd' hgμ.neg_part hsm fun X => hC _
  obtain ⟨jP, cP⟩ := h.2.2 _ hPc hPs hPU
  obtain ⟨jN, cN⟩ := h.2.2 _ hNc hNs hNU
  have kP : Integrable (fun b => s b * ∫ X, max (g X) 0 ∂(m b)) ν :=
    (hsc.mul (continuousOn_univ.1 cP)).integrable_of_hasCompactSupport hss.mul_right
  have kN : Integrable (fun b => s b * ∫ X, max (-g X) 0 ∂(m b)) ν :=
    (hsc.mul (continuousOn_univ.1 cN)).integrable_of_hasCompactSupport hss.mul_right
  have hsplit : ∀ X, g X = max (g X) 0 - max (-g X) 0 := fun X => by
    rcases le_total (g X) 0 with h0 | h0
    · rw [max_eq_right h0, max_eq_left (neg_nonneg.2 h0)]; ring
    · rw [max_eq_left h0, max_eq_right (neg_nonpos.2 h0)]; ring
  have e1 : ∫ X, g X * s (q X) ∂μ =
      ∫ X, max (g X) 0 * s (q X) ∂μ - ∫ X, max (-g X) 0 * s (q X) ∂μ := by
    rw [← integral_sub iP iN]
    refine integral_congr_ae (Eventually.of_forall fun X => ?_)
    show g X * s (q X) = max (g X) 0 * s (q X) - max (-g X) 0 * s (q X)
    rw [← sub_mul, ← hsplit X]
  have e2 : ∫ b, s b * ∫ X, g X ∂(m b) ∂ν =
      ∫ b, s b * ∫ X, max (g X) 0 ∂(m b) ∂ν - ∫ b, s b * ∫ X, max (-g X) 0 ∂(m b) ∂ν := by
    rw [← integral_sub kP kN]
    refine integral_congr_ae (Eventually.of_forall fun b => ?_)
    show s b * ∫ X, g X ∂(m b) =
      s b * ∫ X, max (g X) 0 ∂(m b) - s b * ∫ X, max (-g X) 0 ∂(m b)
    rw [← mul_sub, ← integral_sub (jP b trivial) (jN b trivial)]
    congr 2
    funext X
    exact hsplit X
  rw [e1, e2, hP, hN]

theorem cplx_identity [IsFiniteMeasureOnCompacts ν] (hUm : MeasurableSet U)
    (hι : Function.Injective ι) (hf : ∀ X, ι (q X) = f X)
    (h : IsFibreFamily μ f ι U ν Set.univ m) (hq : Continuous q)
    {φ : V → ℂ} (hφ : Continuous φ) (hφμ : Integrable φ μ)
    {χ : V → ℝ} (hχ : Continuous χ) (hχs : HasCompactSupport χ) (hχU : tsupport χ ⊆ U)
    (hχ01 : ∀ X, 0 ≤ χ X ∧ χ X ≤ 1)
    {s : H → ℝ} (hsc : Continuous s) (hss : HasCompactSupport s) (hs0 : ∀ y, 0 ≤ s y) :
    ∫ X, φ X * (χ X : ℂ) * (s (q X) : ℂ) ∂μ = ∫ b, (s b : ℂ) * ∫ X, φ X * (χ X : ℂ) ∂(m b) ∂ν := by
  obtain ⟨C, hC⟩ := hss.exists_bound_of_continuous hsc
  have hsm : AEStronglyMeasurable (fun X => s (q X)) μ := (hsc.comp hq).aestronglyMeasurable
  have hsup : ∀ a : V → ℝ, Function.support (fun X => a X * χ X) ⊆ Function.support χ :=
    fun a X hX h0 => hX (by simp [show χ X = 0 from h0])
  have hχn : ∀ X, ‖χ X‖ ≤ 1 := fun X => by
    rw [Real.norm_of_nonneg (hχ01 X).1]; exact (hχ01 X).2
  have hp : ∀ a : V → ℝ, Continuous a → Integrable a μ →
      Integrable (fun X => a X * χ X * s (q X)) μ ∧
      (∀ b, Integrable (fun X => a X * χ X) (m b)) ∧
      Integrable (fun b => s b * ∫ X, a X * χ X ∂(m b)) ν ∧
      ∫ X, a X * χ X * s (q X) ∂μ = ∫ b, s b * ∫ X, a X * χ X ∂(m b) ∂ν := fun a ha haμ => by
    have i0 : Integrable (fun X => a X * χ X) μ :=
      integrable_mul_bdd' haμ hχ.aestronglyMeasurable hχn
    obtain ⟨h1, h2⟩ := h.2.2 (fun X => a X * χ X) (ha.mul hχ) (hχs.mono (hsup a))
      ((closure_mono (hsup a)).trans hχU)
    exact ⟨integrable_mul_bdd' i0 hsm fun X => hC _, fun b => h1 b trivial,
      (hsc.mul (continuousOn_univ.1 h2)).integrable_of_hasCompactSupport hss.mul_right,
      real_identity hUm hι hf h hq (ha.mul hχ) (hχs.mono (hsup a))
        ((closure_mono (hsup a)).trans hχU) i0 hsc hss hs0⟩
  obtain ⟨a1, a2, a3, a4⟩ := hp (fun X => (φ X).re) (Complex.continuous_re.comp hφ) hφμ.re
  obtain ⟨b1, b2, b3, b4⟩ := hp (fun X => (φ X).im) (Complex.continuous_im.comp hφ) hφμ.im
  have hid : ∀ X, φ X * (χ X : ℂ) =
      (((φ X).re * χ X : ℝ) : ℂ) + (((φ X).im * χ X : ℝ) : ℂ) * Complex.I := fun X => by
    apply Complex.ext <;> simp
  have hfib : ∀ b, ∫ X, φ X * (χ X : ℂ) ∂(m b) =
      ((∫ X, (φ X).re * χ X ∂(m b) : ℝ) : ℂ) + ((∫ X, (φ X).im * χ X ∂(m b) : ℝ) : ℂ) * Complex.I :=
    fun b => by simp_rw [hid]; exact integral_re_im (a2 b) (b2 b)
  have hl : ∀ X, φ X * (χ X : ℂ) * (s (q X) : ℂ) =
      (((φ X).re * χ X * s (q X) : ℝ) : ℂ) + (((φ X).im * χ X * s (q X) : ℝ) : ℂ) * Complex.I :=
    fun X => by rw [hid]; push_cast; ring
  have hr : ∀ b, (s b : ℂ) * ∫ X, φ X * (χ X : ℂ) ∂(m b) =
      ((s b * ∫ X, (φ X).re * χ X ∂(m b) : ℝ) : ℂ) +
        ((s b * ∫ X, (φ X).im * χ X ∂(m b) : ℝ) : ℂ) * Complex.I :=
    fun b => by rw [hfib]; push_cast; ring
  simp_rw [hl, hr]
  rw [integral_re_im a1 b1, integral_re_im a3 b3, a4, b4]

theorem tail_mu {φ : V → ℂ} (hφ : Continuous φ) (hq : Continuous q) {A : Set V}
    (hA : MeasurableSet A) {ε : ℝ} (hε : 0 ≤ ε)
    (hY : ∀ Y, MeasurableSet Y → ∫⁻ X in Aᶜ ∩ q ⁻¹' Y, ‖φ X‖ₑ ∂μ ≤ ENNReal.ofReal ε * ν Y)
    {χ : V → ℝ} (hχ01 : ∀ X, 0 ≤ χ X ∧ χ X ≤ 1) (hχA : ∀ X ∈ A, χ X = 1)
    {s : H → ℝ} (hsc : Continuous s) (hsi : Integrable s ν) (hs0 : ∀ y, 0 ≤ s y) :
    ‖∫ X, φ X * ((1 - χ X : ℝ) : ℂ) * (s (q X) : ℂ) ∂μ‖ ≤ ε * ∫ y, s y ∂ν := by
  have hsm : Measurable fun y => ENNReal.ofReal (s y) := hsc.measurable.ennreal_ofReal
  have hI : 0 ≤ ∫ y, s y ∂ν := integral_nonneg hs0
  have h3 : ‖∫ X, φ X * ((1 - χ X : ℝ) : ℂ) * (s (q X) : ℂ) ∂μ‖ₑ ≤ ENNReal.ofReal (ε * ∫ y, s y ∂ν) := by
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    calc ∫⁻ X, ‖φ X * ((1 - χ X : ℝ) : ℂ) * (s (q X) : ℂ)‖ₑ ∂μ
        ≤ ∫⁻ X, Aᶜ.indicator (fun X => ‖φ X‖ₑ * ENNReal.ofReal (s (q X))) X ∂μ := by
          refine lintegral_mono fun X => ?_
          by_cases hX : X ∈ A
          · simp [hχA X hX]
          · rw [Set.indicator_of_mem (show X ∈ Aᶜ from hX), enorm_mul, enorm_mul,
              enorm_coe, enorm_coe, ← ofReal_norm_eq_enorm (s (q X)),
              Real.norm_of_nonneg (hs0 _), ← ofReal_norm_eq_enorm (1 - χ X),
              Real.norm_of_nonneg (sub_nonneg.2 (hχ01 X).2)]
            have : ENNReal.ofReal (1 - χ X) ≤ 1 :=
              ENNReal.ofReal_le_one.2 (by linarith [(hχ01 X).1])
            calc ‖φ X‖ₑ * ENNReal.ofReal (1 - χ X) * ENNReal.ofReal (s (q X))
                ≤ ‖φ X‖ₑ * 1 * ENNReal.ofReal (s (q X)) := by gcongr
              _ = _ := by rw [mul_one]
      _ = ∫⁻ X in Aᶜ, ‖φ X‖ₑ * ENNReal.ofReal (s (q X)) ∂μ := lintegral_indicator hA.compl _
      _ ≤ ENNReal.ofReal ε * ∫⁻ y, ENNReal.ofReal (s y) ∂ν :=
          tail_lintegral hφ.measurable hq.measurable hA hY hsm
      _ = ENNReal.ofReal (ε * ∫ y, s y ∂ν) := by
          rw [ENNReal.ofReal_mul hε,
            ofReal_integral_eq_lintegral_ofReal hsi (Eventually.of_forall hs0)]
  rw [← ofReal_norm_eq_enorm] at h3
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hε hI)).1 h3

theorem avg_tendsto [IsFiniteMeasureOnCompacts ν] {F : H → ℂ} (hF : Continuous F) (c : H)
    (r : ℕ → H → ℝ)
    (hr : ∀ k, Continuous (r k) ∧ HasCompactSupport (r k) ∧ (∀ y, 0 ≤ r k y) ∧ 0 < ∫ y, r k y ∂ν)
    (hsh : Tendsto (fun k => tsupport (r k)) atTop (𝓝 c).smallSets) :
    Tendsto (fun k => (∫ y, (r k y : ℂ) * F y ∂ν) / ((∫ y, r k y ∂ν : ℝ) : ℂ)) atTop (𝓝 (F c)) := by
  rw [Metric.tendsto_nhds]
  intro δ hδ
  have hW : F ⁻¹' Metric.ball (F c) (δ / 2) ∈ 𝓝 c :=
    hF.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ (half_pos hδ))
  filter_upwards [(tendsto_smallSets_iff.1 hsh) _ hW] with k hk
  obtain ⟨hc, hcs, h0, hpos⟩ := hr k
  have hri : Integrable (r k) ν := hc.integrable_of_hasCompactSupport hcs
  have hRc : (((∫ y, r k y ∂ν : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hpos.ne'
  have hcs' : HasCompactSupport fun y => (r k y : ℂ) := hcs.comp_left (g := fun x : ℝ => (x : ℂ)) (by simp)
  have hint1 : Integrable (fun y => (r k y : ℂ) * F y) ν :=
    ((Complex.continuous_ofReal.comp hc).mul hF).integrable_of_hasCompactSupport hcs'.mul_right
  have hint2 : Integrable (fun y => (r k y : ℂ)) ν := hri.ofReal
  have hsub : ∫ y, (r k y : ℂ) * (F y - F c) ∂ν =
      (∫ y, (r k y : ℂ) * F y ∂ν) - ((∫ y, r k y ∂ν : ℝ) : ℂ) * F c := by
    simp_rw [mul_sub]
    rw [integral_sub hint1 (hint2.mul_const _), integral_mul_const, integral_complex_ofReal]
  have hdiff : (∫ y, (r k y : ℂ) * F y ∂ν) / ((∫ y, r k y ∂ν : ℝ) : ℂ) - F c =
      (∫ y, (r k y : ℂ) * (F y - F c) ∂ν) / ((∫ y, r k y ∂ν : ℝ) : ℂ) := by
    rw [hsub]
    field_simp
  have hb : ‖∫ y, (r k y : ℂ) * (F y - F c) ∂ν‖ ≤ ∫ y, r k y * (δ / 2) ∂ν := by
    refine norm_integral_le_of_norm_le (hri.mul_const _) (ae_of_all _ fun y => ?_)
    by_cases hy : y ∈ tsupport (r k)
    · have h1 : dist (F y) (F c) < δ / 2 := hk hy
      rw [dist_eq_norm] at h1
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (h0 y)]
      exact mul_le_mul_of_nonneg_left h1.le (h0 y)
    · simp [image_eq_zero_of_notMem_tsupport hy]
  rw [dist_eq_norm, hdiff, norm_div, Complex.norm_real, Real.norm_of_nonneg hpos.le,
    div_lt_iff₀ hpos]
  rw [integral_mul_const] at hb
  nlinarith

end Fib

theorem fibre_avg_tendsto : ∀ (V H Z : Type) [TopologicalSpace V] [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] [TopologicalSpace H] [T2Space H] [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H] (μ : Measure V) (ν : Measure H) [ν.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts ν] (f : V → Z) (ι : H → Z) (q : V → H) (U : Set V) (m : H → Measure V), IsOpen U → Continuous q → Function.Injective ι → (∀ X, ι (q X) = f X) → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν Set.univ m → ∀ φ : V → ℂ, Continuous φ → Integrable φ μ → (∀ ε : ℝ≥0∞, ε ≠ 0 → ∃ A : Set V, IsCompact A ∧ A ⊆ U ∧ ∀ Y, MeasurableSet Y → ∫⁻ X in Aᶜ ∩ q ⁻¹' Y, ‖φ X‖ₑ ∂μ ≤ ε * ν Y) → ∀ c : H, Integrable φ (m c) ∧ ∀ r : ℕ → H → ℝ, (∀ k, Continuous (r k) ∧ HasCompactSupport (r k) ∧ (∀ y, 0 ≤ r k y) ∧ 0 < ∫ y, r k y ∂ν) → Filter.Tendsto (fun k => tsupport (r k)) Filter.atTop (nhds c).smallSets → Filter.Tendsto (fun k => (∫ X, φ X * (r k (q X) : ℂ) ∂μ) / ((∫ y, r k y ∂ν : ℝ) : ℂ)) Filter.atTop (nhds (∫ X, φ X ∂(m c))) := by
  intro V H Z _ _ _ _ _ _ _ _ _ _ _ μ ν _ _ f ι q U m hU hq hι hf h φ hφ hφμ hD c
  have get : ∀ ε : ℝ, 0 < ε → ∃ (A : Set V) (χ : V → ℝ), MeasurableSet A ∧
      (∀ Y, MeasurableSet Y → ∫⁻ X in Aᶜ ∩ q ⁻¹' Y, ‖φ X‖ₑ ∂μ ≤ ENNReal.ofReal ε * ν Y) ∧
      Continuous χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ U ∧ (∀ X, 0 ≤ χ X ∧ χ X ≤ 1) ∧
      ∀ X ∈ A, χ X = 1 := by
    intro ε hε
    obtain ⟨A, hAc, hAU, hY⟩ := hD (ENNReal.ofReal ε) (ENNReal.ofReal_ne_zero_iff.2 hε)
    obtain ⟨χ, h1, h2, h3, h4⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hAc hU hAU
    exact ⟨A, χ, hAc.isClosed.measurableSet, hY, χ.continuous, h2, h3, fun X => h4 X, fun X hX => h1 hX⟩
  have hint : Integrable φ (m c) := by
    obtain ⟨A, χ, hAm, hY, hχ, hχs, hχU, hχ01, hχA⟩ := get 1 one_pos
    exact fibre_integrable hφ h hχ hχs hχU hχ01
      ((fibre_tail hU hι hf h hq.measurable hφ hAm hY hχ hχ01 hχA c).trans_lt ENNReal.ofReal_lt_top)
  refine ⟨hint, fun r hr hsh => ?_⟩
  rw [Metric.tendsto_nhds]
  intro δ hδ
  have hδ4 : 0 < δ / 4 := by positivity
  obtain ⟨A, χ, hAm, hY, hχ, hχs, hχU, hχ01, hχA⟩ := get (δ / 4) hδ4
  obtain ⟨hfi, hFc⟩ := fibre_cut hφ h hχ hχs hχU
  have hd := fibre_diff hint (hfi c) hχ01 hδ4.le
    (fibre_tail hU hι hf h hq.measurable hφ hAm hY hχ hχ01 hχA c)
  filter_upwards [(Metric.tendsto_nhds.1 (avg_tendsto hFc c r hr hsh)) (δ / 4) hδ4] with k hk
  obtain ⟨hc, hcs, h0, hpos⟩ := hr k
  have hri : Integrable (r k) ν := hc.integrable_of_hasCompactSupport hcs
  obtain ⟨C, hC⟩ := hcs.exists_bound_of_continuous hc
  have hrq : AEStronglyMeasurable (fun X => (r k (q X) : ℂ)) μ :=
    (Complex.continuous_ofReal.comp (hc.comp hq)).aestronglyMeasurable
  have hrqb : ∀ X, ‖(r k (q X) : ℂ)‖ ≤ C := fun X => by rw [Complex.norm_real]; exact hC _
  have i1 : Integrable (fun X => φ X * (χ X : ℂ) * (r k (q X) : ℂ)) μ :=
    integrable_mul_bdd' (integrable_mul_bdd' hφμ
      (Complex.continuous_ofReal.comp hχ).aestronglyMeasurable (C := 1) (fun X => by
        rw [Complex.norm_real, Real.norm_of_nonneg (hχ01 X).1]; exact (hχ01 X).2)) hrq hrqb
  have i2 : Integrable (fun X => φ X * ((1 - χ X : ℝ) : ℂ) * (r k (q X) : ℂ)) μ :=
    integrable_mul_bdd' (integrable_mul_bdd' hφμ
      (Complex.continuous_ofReal.comp (continuous_const.sub hχ)).aestronglyMeasurable (C := 1)
      (fun X => by
        rw [Complex.norm_real, Real.norm_of_nonneg (sub_nonneg.2 (hχ01 X).2)]
        linarith [(hχ01 X).1])) hrq hrqb
  have hsplit : ∫ X, φ X * (r k (q X) : ℂ) ∂μ =
      (∫ y, (r k y : ℂ) * ∫ X, φ X * (χ X : ℂ) ∂(m y) ∂ν) +
        ∫ X, φ X * ((1 - χ X : ℝ) : ℂ) * (r k (q X) : ℂ) ∂μ := by
    rw [← cplx_identity hU.measurableSet hι hf h hq hφ hφμ hχ hχs hχU hχ01 hc hcs h0,
      ← integral_add i1 i2]
    refine integral_congr_ae (Eventually.of_forall fun X => ?_)
    show φ X * (r k (q X) : ℂ) = _
    push_cast
    ring
  have ht := tail_mu hφ hq hAm hδ4.le hY hχ01 hχA hc hri h0
  have ht' : ‖(∫ X, φ X * ((1 - χ X : ℝ) : ℂ) * (r k (q X) : ℂ) ∂μ) / ((∫ y, r k y ∂ν : ℝ) : ℂ)‖ ≤ δ / 4 := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hpos.le]
    exact (div_le_iff₀ hpos).2 ht
  rw [dist_eq_norm] at hk ⊢
  rw [hsplit, add_div]
  set a := (∫ y, (r k y : ℂ) * ∫ X, φ X * (χ X : ℂ) ∂(m y) ∂ν) / ((∫ y, r k y ∂ν : ℝ) : ℂ)
  set b := (∫ X, φ X * ((1 - χ X : ℝ) : ℂ) * (r k (q X) : ℂ) ∂μ) / ((∫ y, r k y ∂ν : ℝ) : ℂ)
  set Fc := ∫ X, φ X * (χ X : ℂ) ∂(m c)
  set d := ∫ X, φ X ∂(m c)
  have hfin : a + b - d = (a - Fc) + b - (d - Fc) := by ring
  rw [hfin]
  calc ‖(a - Fc) + b - (d - Fc)‖ ≤ ‖(a - Fc) + b‖ + ‖d - Fc‖ := norm_sub_le _ _
    _ ≤ ‖a - Fc‖ + ‖b‖ + ‖d - Fc‖ := by gcongr; exact norm_add_le _ _
    _ < δ := by linarith

end GlobalTheory.CompanionTheory.WhitFree.AvgInf.Lim
