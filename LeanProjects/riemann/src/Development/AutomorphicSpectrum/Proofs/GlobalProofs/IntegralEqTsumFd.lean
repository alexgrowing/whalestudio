import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsCovolOne
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.EqZeroOfFourierCoefficientsVanish
import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.FdSetIntegralCharEqZero
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AdlEqZeroOfMemNbhd

noncomputable section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal Matrix

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.PoiAbs

section Gen

variable {V C : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [LocallyCompactSpace V]
  [T2Space V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] [AddCommGroup C] [Countable C]

def per (ι : C →+ V) (f : V → ℂ) (b : V) : ℂ := ∑' c, f (b + ι c)

def UnifSummable (ι : C →+ V) (f : V → ℂ) : Prop :=
  ∀ K : Set V, IsCompact K → ∃ u : C → ℝ, Summable u ∧ ∀ c : C, ∀ b ∈ K, ‖f (b + ι c)‖ ≤ u c

theorem continuous_per {ι : C →+ V} {f : V → ℂ} (hf : Continuous f) (h : UnifSummable ι f) :
    Continuous (per ι f) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  obtain ⟨K, hK, hxK⟩ := exists_compact_mem_nhds x
  obtain ⟨u, hu, hb⟩ := h K hK
  have : ContinuousOn (per ι f) K :=
    continuousOn_tsum (fun c => (hf.comp (continuous_id.add continuous_const)).continuousOn) hu
      (fun c b hb' => hb c b hb')
  exact this.continuousAt hxK

theorem per_add (ι : C →+ V) (f : V → ℂ) (x : V) (c : C) : per ι f (x + ι c) = per ι f x := by
  unfold per
  rw [← (Equiv.addLeft c).tsum_eq (fun d => f (x + ι d))]
  refine tsum_congr fun d => ?_
  simp [add_assoc]

theorem per_bounded {ι : C →+ V} {f : V → ℂ} (h : UnifSummable ι f) {K : Set V} (hK : IsCompact K)
    (hx : ∀ x, ∃ a, x - ι a ∈ K) : ∃ M, ∀ x, ‖per ι f x‖ ≤ M := by
  obtain ⟨u, hu, hb⟩ := h K hK
  refine ⟨∑' c, u c, fun x => ?_⟩
  obtain ⟨a, ha⟩ := hx x
  have e : per ι f x = per ι f (x - ι a) := by
    rw [← per_add ι f (x - ι a) a, sub_add_cancel]
  rw [e]
  exact tsum_of_norm_bounded hu.hasSum fun c => hb c _ ha

theorem integrableOn_bdd {μ : Measure V} {D : Set V} (hD : μ D ≠ ∞) {g : V → ℂ} (hg : Continuous g)
    {M : ℝ} (hM : ∀ x, ‖g x‖ ≤ M) : IntegrableOn g D μ :=
  Measure.integrableOn_of_bounded hD hg.aestronglyMeasurable (Filter.Eventually.of_forall hM)

theorem integrable_of_unif {ι : C →+ V} {f : V → ℂ} (hf : Continuous f) (h : UnifSummable ι f)
    (μ : Measure V) [μ.IsAddHaarMeasure] {K : Set V} (hK : IsCompact K) (hx : ∀ x, ∃ a, x - ι a ∈ K) :
    Integrable f μ := by
  obtain ⟨u, hu, hb⟩ := h K hK
  obtain ⟨k, hk⟩ : K.Nonempty := by
    obtain ⟨a, ha⟩ := hx 0
    exact ⟨_, ha⟩
  have hu0 : ∀ a, 0 ≤ u a := fun a => (norm_nonneg _).trans (hb a k hk)
  let s : C → TopologicalSpace.Compacts V := fun a =>
    ⟨(fun y => y + ι a) '' K, hK.image (continuous_id.add continuous_const)⟩
  let G : C(V, ℂ) := ⟨f, hf⟩
  have hs : ⋃ a, (s a : Set V) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    obtain ⟨a, ha⟩ := hx x
    exact ⟨a, x - ι a, ha, sub_add_cancel _ _⟩
  have hμ : ∀ a, μ.real (s a : Set V) = μ.real K := by
    intro a
    have : ((s a : TopologicalSpace.Compacts V) : Set V) = (fun y => y + -ι a) ⁻¹' K := by
      show (fun y => y + ι a) '' K = _
      rw [Set.image_add_right]
    rw [this, Measure.real, Measure.real, measure_preimage_add_right]
  have hn : ∀ a, ‖G.restrict (s a : Set V)‖ ≤ u a := by
    intro a
    rw [ContinuousMap.norm_le _ (hu0 a)]
    rintro ⟨y, b, hb', rfl⟩
    exact hb a b hb'
  refine integrable_of_summable_norm_restrict (f := G) (s := s) ?_ hs
  refine Summable.of_nonneg_of_le (fun _ => mul_nonneg (norm_nonneg _) measureReal_nonneg) (fun a => ?_)
    (hu.mul_right (μ.real K))
  rw [hμ]
  exact mul_le_mul_of_nonneg_right (hn a) measureReal_nonneg

theorem countable_range (ι : C →+ V) : Countable ι.range :=
  ι.rangeRestrict_surjective.countable

theorem summable_fd {ι : C →+ V} (hι : Function.Injective ι) {μ : Measure V} [μ.IsAddHaarMeasure]
    {D : Set V} (hD : IsAddFundamentalDomain ι.range D μ) {h : V → ℂ} (hh : Integrable h μ) :
    Summable fun c => ∫ x in D, ‖h (x + ι c)‖ ∂μ := by
  have := countable_range ι
  have hsum := hD.lintegral_eq_tsum'' (fun x => ‖h x‖ₑ)
  have hfin : ∑' g : ι.range, ∫⁻ x in D, ‖h (g +ᵥ x)‖ₑ ∂μ ≠ ∞ := by
    rw [← hsum]
    exact hh.2.ne
  have hs := ENNReal.summable_toReal hfin
  have h2 := ((ι.ofInjective hι).toEquiv.summable_iff).2 hs
  refine h2.congr fun c => ?_
  rw [integral_norm_eq_lintegral_enorm (hh.comp_add_right (ι c)).integrableOn.aestronglyMeasurable]
  have : ∀ x, ((ι.ofInjective hι).toEquiv c : ι.range) +ᵥ x = x + ι c := fun x => by
    show ι c + x = x + ι c
    exact add_comm _ _
  simp only [Function.comp, this]

theorem integral_eq_tsum_fd {ι : C →+ V} (hι : Function.Injective ι) {μ : Measure V} [μ.IsAddHaarMeasure]
    {D : Set V} (hD : IsAddFundamentalDomain ι.range D μ) {h : V → ℂ} (hh : Integrable h μ) :
    ∫ x, h x ∂μ = ∑' c, ∫ x in D, h (x + ι c) ∂μ := by
  have := countable_range ι
  rw [hD.integral_eq_tsum'' h hh, ← (ι.ofInjective hι).toEquiv.tsum_eq]
  refine tsum_congr fun c => ?_
  have : ∀ x, ((ι.ofInjective hι).toEquiv c : ι.range) +ᵥ x = x + ι c := fun x => by
    show ι c + x = x + ι c
    exact add_comm _ _
  simp only [this]

theorem setIntegral_tsum_fd {ι : C →+ V} (hι : Function.Injective ι) {μ : Measure V} [μ.IsAddHaarMeasure]
    {D : Set V} (hD : IsAddFundamentalDomain ι.range D μ) {h : V → ℂ} (hh : Integrable h μ) :
    ∫ x in D, ∑' c, h (x + ι c) ∂μ = ∫ x, h x ∂μ := by
  have hs := hasSum_integral_of_summable_integral_norm (μ := μ.restrict D)
    (F := fun c x => h (x + ι c))
    (fun c => (hh.comp_add_right (ι c)).integrableOn) (summable_fd hι hD hh)
  rw [integral_eq_tsum_fd hι hD hh]
  exact hs.tsum_eq.symm

theorem per_unfold {ι : C →+ V} (hι : Function.Injective ι) {μ : Measure V} [μ.IsAddHaarMeasure]
    {D : Set V} (hD : IsAddFundamentalDomain ι.range D μ) {f e : V → ℂ} (hfi : Integrable f μ)
    (he : Continuous e) (hen : ∀ x, ‖e x‖ = 1) (hep : ∀ x c, e (x + ι c) = e x) :
    ∫ b in D, per ι f b * e b ∂μ = ∫ b, f b * e b ∂μ := by
  have hh : Integrable (fun b => f b * e b) μ :=
    hfi.mono (hfi.aestronglyMeasurable.mul he.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => by simp [hen])
  rw [← setIntegral_tsum_fd hι hD hh]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show per ι f x * e x = ∑' c, f (x + ι c) * e (x + ι c)
  simp only [hep]
  exact tsum_mul_right.symm

def ser (a : C → ℂ) (E : C → V → ℂ) (b : V) : ℂ := ∑' t, a t * E t b

theorem continuous_ser {a : C → ℂ} (ha : Summable fun t => ‖a t‖) {E : C → V → ℂ}
    (hEc : ∀ t, Continuous (E t)) (hEn : ∀ t b, ‖E t b‖ = 1) : Continuous (ser a E) :=
  continuous_tsum (fun t => continuous_const.mul (hEc t)) ha (fun t b => by simp [hEn])

theorem norm_ser_le {a : C → ℂ} (ha : Summable fun t => ‖a t‖) {E : C → V → ℂ}
    (hEn : ∀ t b, ‖E t b‖ = 1) (b : V) : ‖ser a E b‖ ≤ ∑' t, ‖a t‖ :=
  tsum_of_norm_bounded ha.hasSum fun t => by simp [hEn]

theorem coef_ser {a : C → ℂ} (ha : Summable fun t => ‖a t‖) {E : C → V → ℂ}
    (hEc : ∀ t, Continuous (E t)) (hEn : ∀ t b, ‖E t b‖ = 1) {μ : Measure V} {D : Set V}
    (hD1 : μ D = 1) (hself : ∀ t x, E t x * E (-t) x = 1)
    (horth : ∀ s t, t ≠ s → ∫ x in D, E t x * E (-s) x ∂μ = 0) (s : C) :
    ∫ x in D, ser a E x * E (-s) x ∂μ = a s := by
  classical
  have hDf : μ D ≠ ∞ := by rw [hD1]; exact ENNReal.one_ne_top
  have hr : μ.real D = 1 := by simp [Measure.real, hD1]
  have hint : ∀ t, IntegrableOn (fun x => a t * E t x * E (-s) x) D μ := fun t =>
    integrableOn_bdd hDf ((continuous_const.mul (hEc t)).mul (hEc (-s))) (M := ‖a t‖)
      (fun x => by simp [hEn])
  have hn : ∀ t, ∫ x in D, ‖a t * E t x * E (-s) x‖ ∂μ = ‖a t‖ := fun t => by
    simp [hEn, hr]
  have hs := hasSum_integral_of_summable_integral_norm (μ := μ.restrict D)
    (F := fun t x => a t * E t x * E (-s) x) hint (by simpa only [hn] using ha)
  have hval : ∀ t, t ≠ s → ∫ x in D, a t * E t x * E (-s) x ∂μ = 0 := fun t ht => by
    simp only [mul_assoc]
    rw [integral_const_mul, horth s t ht, mul_zero]
  have hs1 : ∫ x in D, a s * E s x * E (-s) x ∂μ = a s := by
    simp only [mul_assoc, hself]
    simp [hr]
  have h1 := hasSum_single (f := fun t => ∫ x in D, a t * E t x * E (-s) x ∂μ) s
    (fun t ht => hval t ht)
  have h2 := hs.unique h1
  rw [hs1] at h2
  rw [← h2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show ser a E x * E (-s) x = ∑' t, a t * E t x * E (-s) x
  simp only [ser, tsum_mul_right]

theorem poisson_gen {ι : C →+ V} (hι : Function.Injective ι) {μ : Measure V} [μ.IsAddHaarMeasure]
    {D : Set V} (hD : IsAddFundamentalDomain ι.range D μ) (hD1 : μ D = 1) {K : Set V}
    (hK : IsCompact K) (hx : ∀ x, ∃ a, x - ι a ∈ K) {E : C → V → ℂ}
    (hEc : ∀ t, Continuous (E t)) (hEn : ∀ t b, ‖E t b‖ = 1) (hEp : ∀ t x c, E t (x + ι c) = E t x)
    (hE0 : ∀ t, E t 0 = 1) (hself : ∀ t x, E t x * E (-t) x = 1)
    (horth : ∀ s t, t ≠ s → ∫ x in D, E t x * E (-s) x ∂μ = 0)
    (hcomp : ∀ g : V → ℂ, Continuous g → (∀ x c, g (x + ι c) = g x) →
      (∀ t, ∫ b in D, g b * E (-t) b ∂μ = 0) → ∀ x, g x = 0)
    {f : V → ℂ} (hf : Continuous f) (h : UnifSummable ι f) :
    Integrable f μ ∧ (Summable (fun t => ∫ b, f b * E (-t) b ∂μ) →
      ∑' c, f (ι c) = ∑' t, ∫ b, f b * E (-t) b ∂μ) := by
  have hfi := integrable_of_unif hf h μ hK hx
  refine ⟨hfi, fun hsum => ?_⟩
  have hDf : μ D ≠ ∞ := by rw [hD1]; exact ENNReal.one_ne_top
  set a : C → ℂ := fun t => ∫ b, f b * E (-t) b ∂μ with hadef
  have ha : Summable fun t => ‖a t‖ := hsum.norm
  have hP := continuous_per hf h
  have hS := continuous_ser ha hEc hEn
  obtain ⟨M, hM⟩ := per_bounded h hK hx
  have hperS : ∀ x c, ser a E (x + ι c) = ser a E x := fun x c => by
    simp only [ser, hEp]
  have hz := hcomp (fun x => per ι f x - ser a E x) (hP.sub hS)
    (fun x c => by simp only [per_add, hperS]) (fun t => ?_) 0
  · have e1 : per ι f 0 = ∑' c, f (ι c) := by simp [per]
    have e2 : ser a E 0 = ∑' t, a t := by simp [ser, hE0]
    rw [← e1, ← e2]
    exact sub_eq_zero.1 hz
  · have i1 : IntegrableOn (fun b => per ι f b * E (-t) b) D μ :=
      integrableOn_bdd hDf (hP.mul (hEc _)) (M := M) (fun x => by simpa [hEn] using hM x)
    have i2 : IntegrableOn (fun b => ser a E b * E (-t) b) D μ :=
      integrableOn_bdd hDf (hS.mul (hEc _)) (M := ∑' t, ‖a t‖)
        (fun x => by simpa [hEn] using norm_ser_le ha hEn x)
    simp only [sub_mul]
    rw [integral_sub i1 i2, per_unfold hι hD hfi (hEc _) (hEn _) (hEp _),
      coef_ser ha hEc hEn hD1 hself horth t, sub_eq_zero]

end Gen

section Adelic

end Adelic
end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.PoiAbs
