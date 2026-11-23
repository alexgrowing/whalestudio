import Mathlib
import Formalism.UnipotentAdelicQuotients.SWXSDefs
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.MeasureEqHaarProdOfLeftInvariant
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.SW.Slice

theorem comap_map_of_intertwine {W V : Type} [MeasurableSpace W] [MeasurableSpace V]
    {T : W → V} (hT : MeasurableEmbedding T) {L L' : W → W} {A A' : V → V}
    (hL : Measurable L) (hA : Measurable A) (hLL' : ∀ w, L (L' w) = w)
    (hAA' : ∀ v, A' (A v) = v)
    (hint : ∀ w, T (L w) = A (T w)) (hint' : ∀ w, T (L' w) = A' (T w))
    (μ : Measure V) (c : ℝ≥0∞) (hμ : μ.map A = c • μ) :
    (μ.comap T).map L = c • μ.comap T := by
  ext s hs
  have himg : T '' (L ⁻¹' s) = A ⁻¹' (T '' s) := by
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨L w, hw, hint w⟩
    · rintro ⟨y, hy, hyv⟩
      refine ⟨L' y, ?_, ?_⟩
      · change L (L' y) ∈ s
        rwa [hLL']
      · rw [hint', hyv, hAA']
  rw [Measure.map_apply hL hs, Measure.smul_apply, hT.comap_apply, hT.comap_apply, himg,
    ← Measure.map_apply hA (hT.measurableSet_image.2 hs), hμ, Measure.smul_apply]

theorem withDensity_map_of_scale {W : Type} [MeasurableSpace W] {L : W → W} (hL : Measurable L)
    (ρ : Measure W) (c k : ℝ≥0∞) (hρ : ρ.map L = c • ρ) {d : W → ℝ≥0∞} (hd : Measurable d)
    (hk : ∀ w, d w = k * d (L w)) (hck : k * c = 1) :
    (ρ.withDensity d).map L = ρ.withDensity d := by
  ext s hs
  rw [Measure.map_apply hL hs, withDensity_apply _ (hL hs), withDensity_apply _ hs]
  calc ∫⁻ w in L ⁻¹' s, d w ∂ρ = ∫⁻ w, (L ⁻¹' s).indicator d w ∂ρ :=
        (lintegral_indicator (hL hs) _).symm
    _ = ∫⁻ w, k * s.indicator d (L w) ∂ρ := by
        refine lintegral_congr fun w => ?_
        by_cases hw : L w ∈ s
        · rw [Set.indicator_of_mem (show w ∈ L ⁻¹' s from hw), Set.indicator_of_mem hw, ← hk]
        · rw [Set.indicator_of_notMem (show w ∉ L ⁻¹' s from hw), Set.indicator_of_notMem hw,
            mul_zero]
    _ = k * ∫⁻ w, s.indicator d (L w) ∂ρ :=
        lintegral_const_mul _ ((hd.indicator hs).comp hL)
    _ = k * ∫⁻ w, s.indicator d w ∂(ρ.map L) := by
        rw [lintegral_map (hd.indicator hs) hL]
    _ = ∫⁻ w in s, d w ∂ρ := by
        rw [hρ, lintegral_smul_measure, smul_eq_mul, ← mul_assoc, hck, one_mul,
          lintegral_indicator hs]

theorem comap_isLocallyFinite {W V : Type} [TopologicalSpace W] [MeasurableSpace W]
    [TopologicalSpace V] [MeasurableSpace V] [BorelSpace W] [BorelSpace V] {T : W → V}
    (hT : IsOpenEmbedding T) (μ : Measure V) [IsLocallyFiniteMeasure μ] :
    IsLocallyFiniteMeasure (μ.comap T) := by
  refine ⟨fun x => ?_⟩
  obtain ⟨s, hxs, hs, hfin⟩ := μ.exists_isOpen_measure_lt_top (T x)
  have hme : MeasurableEmbedding T := hT.measurableEmbedding
  refine ⟨T ⁻¹' s, (hs.preimage hT.continuous).mem_nhds hxs, ?_⟩
  rw [hme.comap_apply]
  exact lt_of_le_of_lt (measure_mono (Set.image_preimage_subset _ _)) hfin

section Theta

variable {V X Q : Type} [TopologicalSpace V] [TopologicalSpace X] [Group Q] [TopologicalSpace Q]
  [IsTopologicalGroup Q] [MulAction Q V] [ContinuousSMul Q V] [MulAction Q X] [ContinuousSMul Q X]

def theta (g : V → X) (b₀ : X) (p : Q × (g ⁻¹' {b₀})) : V := p.1 • (p.2 : V)

theorem continuous_theta (g : V → X) (b₀ : X) : Continuous (theta (Q := Q) g b₀) :=
  continuous_fst.smul (continuous_subtype_val.comp continuous_snd)

theorem theta_isOpenEmbedding [T2Space X] {g : V → X} (hg : Continuous g)
    (heq : ∀ (q : Q) (v : V), g (q • v) = q • g v) {b₀ : X}
    (ho : IsOpenEmbedding (fun q : Q => q • b₀)) :
    IsOpenEmbedding (theta (Q := Q) g b₀) ∧
      Set.range (theta (Q := Q) g b₀) = g ⁻¹' Set.range (fun q : Q => q • b₀) := by
  classical
  set o : Q → X := fun q : Q => q • b₀ with ho_def
  have hB : IsOpen (Set.range o) := ho.isOpen_range
  have hU : IsOpen (g ⁻¹' Set.range o) := hB.preimage hg
  let he : Q ≃ₜ Set.range o := ho.isEmbedding.toHomeomorph
  let s : (g ⁻¹' Set.range o) → Q := fun v => he.symm ⟨g v, v.2⟩
  have hs_cont : Continuous s :=
    he.symm.continuous.comp ((hg.comp continuous_subtype_val).subtype_mk _)
  have hs : ∀ v, s v • b₀ = g v := fun v => by
    have := he.apply_symm_apply ⟨g v, v.2⟩
    exact congrArg Subtype.val this
  have hmem : ∀ v : (g ⁻¹' Set.range o), (s v)⁻¹ • (v : V) ∈ g ⁻¹' {b₀} := fun v => by
    change g ((s v)⁻¹ • (v : V)) = b₀
    rw [heq, ← hs v, inv_smul_smul]
  let t : (g ⁻¹' Set.range o) → Q × (g ⁻¹' {b₀}) := fun v => (s v, ⟨(s v)⁻¹ • (v : V), hmem v⟩)
  have ht_cont : Continuous t :=
    hs_cont.prodMk ((hs_cont.inv.smul continuous_subtype_val).subtype_mk _)
  have hgθ : ∀ p : Q × (g ⁻¹' {b₀}), g (theta g b₀ p) = o p.1 := fun p => by
    have hz : g (p.2 : V) = b₀ := p.2.2
    simp only [theta, heq, hz, ho_def]
  have hθU : ∀ p : Q × (g ⁻¹' {b₀}), theta g b₀ p ∈ g ⁻¹' Set.range o := fun p =>
    ⟨p.1, (hgθ p).symm⟩
  have hθt : ∀ v : (g ⁻¹' Set.range o), theta g b₀ (t v) = v := fun v => by
    simp only [theta, t, smul_inv_smul]
  have htθ : ∀ p : Q × (g ⁻¹' {b₀}), t ⟨theta g b₀ p, hθU p⟩ = p := fun p => by
    have h1 : s ⟨theta g b₀ p, hθU p⟩ = p.1 := ho.injective (by
      change s _ • b₀ = _
      rw [hs]
      exact hgθ p)
    refine Prod.ext h1 (Subtype.ext ?_)
    change (s ⟨theta g b₀ p, hθU p⟩)⁻¹ • theta g b₀ p = (p.2 : V)
    rw [h1]
    simp only [theta, inv_smul_smul]
  have hinj : Function.Injective (theta (Q := Q) g b₀) := fun p p' h => by
    rw [← htθ p, ← htθ p']
    congr 2
  have hopen : IsOpenMap (theta (Q := Q) g b₀) := fun W hW => by
    have : theta g b₀ '' W = Subtype.val '' (t ⁻¹' W) := by
      ext v
      constructor
      · rintro ⟨p, hp, rfl⟩
        exact ⟨⟨theta g b₀ p, hθU p⟩, by simpa [htθ p] using hp, rfl⟩
      · rintro ⟨u, hu, rfl⟩
        exact ⟨t u, hu, hθt u⟩
    rw [this]
    exact hU.isOpenMap_subtype_val _ (hW.preimage ht_cont)
  refine ⟨.of_continuous_injective_isOpenMap (continuous_theta g b₀) hinj hopen, ?_⟩
  ext v
  constructor
  · rintro ⟨p, rfl⟩
    exact hθU p
  · intro hv
    exact ⟨t ⟨v, hv⟩, hθt ⟨v, hv⟩⟩

end Theta

section Core

variable {V X Q : Type} [TopologicalSpace V] [SecondCountableTopology V]
  [MeasurableSpace V] [BorelSpace V]
  [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
  [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [LocallyCompactSpace Q]
  [SecondCountableTopology Q] [T2Space Q] [MeasurableSpace Q] [BorelSpace Q]
  [MulAction Q V] [ContinuousSMul Q V] [MulAction Q X] [ContinuousSMul Q X]

noncomputable def fibFam (g : V → X) (b₀ : X) (w : Q → ℝ≥0) (m : Measure (g ⁻¹' {b₀})) (b : X) :
    Measure V :=
  open Classical in
  if b ∈ Set.range (fun q : Q => q • b₀) then
    (w (Function.invFun (fun q : Q => q • b₀) b) : ℝ≥0∞) •
      m.map (fun z : (g ⁻¹' {b₀}) => Function.invFun (fun q : Q => q • b₀) b • (z : V))
  else 0

theorem fibFam_orbit {g : V → X} {b₀ : X} (w : Q → ℝ≥0) (m : Measure (g ⁻¹' {b₀}))
    (ho : Function.Injective (fun q : Q => q • b₀)) (q : Q) :
    fibFam g b₀ w m (q • b₀) = (w q : ℝ≥0∞) • m.map (fun z : (g ⁻¹' {b₀}) => q • (z : V)) := by
  have h : Function.invFun (fun q : Q => q • b₀) (q • b₀) = q :=
    Function.leftInverse_invFun ho q
  rw [fibFam, if_pos ⟨q, rfl⟩, h]

theorem fibFam_off {g : V → X} {b₀ : X} (w : Q → ℝ≥0) (m : Measure (g ⁻¹' {b₀})) {b : X}
    (hb : b ∉ Set.range (fun q : Q => q • b₀)) : fibFam g b₀ w m b = 0 := by
  rw [fibFam, if_neg hb]

theorem continuous_smul_fib (g : V → X) (b₀ : X) (q : Q) :
    Continuous (fun z : (g ⁻¹' {b₀}) => q • (z : V)) :=
  continuous_const.smul continuous_subtype_val

theorem fibFam_support {Y : Type} {f : V → Y} {g : V → X} {ι : X → Y} (hι : Function.Injective ι)
    (hg : Continuous g) (hf : ∀ v, f v = ι (g v))
    (heq : ∀ (q : Q) (v : V), g (q • v) = q • g v) {b₀ : X}
    (ho : IsOpenEmbedding (fun q : Q => q • b₀)) (w : Q → ℝ≥0) (m : Measure (g ⁻¹' {b₀}))
    (b : X) :
    fibFam g b₀ w m b (f ⁻¹' {ι b} ∩ g ⁻¹' Set.range (fun q : Q => q • b₀))ᶜ = 0 := by
  by_cases hb : b ∈ Set.range (fun q : Q => q • b₀)
  · obtain ⟨q, rfl⟩ := hb
    have hfib : f ⁻¹' {ι (q • b₀)} = g ⁻¹' {q • b₀} := by
      ext v
      simp only [Set.mem_preimage, Set.mem_singleton_iff, hf]
      exact hι.eq_iff
    have hBm : MeasurableSet (Set.range (fun q : Q => q • b₀)) :=
      ho.isOpen_range.measurableSet
    have hS : MeasurableSet (f ⁻¹' {ι (q • b₀)} ∩ g ⁻¹' Set.range (fun q : Q => q • b₀))ᶜ := by
      rw [hfib]
      exact ((hg.measurable (measurableSet_singleton _)).inter (hg.measurable hBm)).compl
    change fibFam g b₀ w m ((fun q : Q => q • b₀) q) _ = 0
    change fibFam g b₀ w m (q • b₀) _ = 0
    rw [fibFam_orbit w m ho.injective, Measure.smul_apply,
      Measure.map_apply (continuous_smul_fib g b₀ q).measurable hS]
    have : (fun z : (g ⁻¹' {b₀}) => q • (z : V)) ⁻¹'
        (f ⁻¹' {ι (q • b₀)} ∩ g ⁻¹' Set.range (fun q : Q => q • b₀))ᶜ = ∅ := by
      ext z
      have hz : g (z : V) = b₀ := z.2
      simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_singleton_iff,
        hf, heq, hz, Set.mem_empty_iff_false, iff_false, not_not]
      exact ⟨trivial, ⟨q, rfl⟩⟩
    rw [this]
    simp
  · rw [fibFam_off w m hb]
    simp

theorem exists_compact_fib [T2Space V] {g : V → X} (hg : Continuous g) (b₀ : X) {K : Set Q}
    (hK : IsCompact K) {S : Set V} (hS : IsCompact S) :
    ∃ k : Set (g ⁻¹' {b₀}), IsCompact k ∧ ∀ q ∈ K, ∀ z : (g ⁻¹' {b₀}), q • (z : V) ∈ S → z ∈ k := by
  have hcl : IsClosed (g ⁻¹' {b₀}) := isClosed_singleton.preimage hg
  have hc : IsCompact ((fun p : Q × V => p.1⁻¹ • p.2) '' (K ×ˢ S)) :=
    (hK.prod hS).image (continuous_fst.inv.smul continuous_snd)
  refine ⟨Subtype.val ⁻¹' ((fun p : Q × V => p.1⁻¹ • p.2) '' (K ×ˢ S)),
    hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hc, fun q hq z hz => ?_⟩
  exact ⟨(q, q • (z : V)), ⟨hq, hz⟩, by simp⟩

theorem integrable_and_continuous [T2Space V] {g : V → X} (hg : Continuous g) {b₀ : X}
    (ho : IsOpenEmbedding (fun q : Q => q • b₀)) {w : Q → ℝ≥0} (hw : Continuous w)
    (m : Measure (g ⁻¹' {b₀})) [IsLocallyFiniteMeasure m] {φ : V → ℝ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) :
    (∀ b ∈ Set.range (fun q : Q => q • b₀), Integrable φ (fibFam g b₀ w m b)) ∧
      ContinuousOn (fun b => ∫ v, φ v ∂(fibFam g b₀ w m b))
        (Set.range (fun q : Q => q • b₀)) := by
  have hvan : ∀ {K : Set Q} {k : Set (g ⁻¹' {b₀})},
      (∀ q ∈ K, ∀ z : (g ⁻¹' {b₀}), q • (z : V) ∈ tsupport φ → z ∈ k) →
      ∀ q, ∀ z : (g ⁻¹' {b₀}), q ∈ K → z ∉ k → φ (q • (z : V)) = 0 := by
    intro K k hk q z hq hz
    by_contra hne
    exact hz (hk q hq z (subset_tsupport _ hne))
  have hint : ∀ q : Q, Integrable (fun z : (g ⁻¹' {b₀}) => φ (q • (z : V))) m := by
    intro q
    obtain ⟨k, hk, hkz⟩ := exists_compact_fib hg b₀ (isCompact_singleton (x := q)) hφc
    refine (hφ.comp (continuous_smul_fib g b₀ q)).integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.intro hk fun z hz => ?_
    exact hvan hkz q z rfl hz
  have hval : ∀ q : Q, ∫ v, φ v ∂(fibFam g b₀ w m (q • b₀)) =
      (w q : ℝ) * ∫ z, φ (q • (z : V)) ∂m := by
    intro q
    rw [fibFam_orbit w m ho.injective, integral_smul_measure,
      integral_map (continuous_smul_fib g b₀ q).aemeasurable hφ.aestronglyMeasurable]
    simp
  have hG : Continuous (fun q : Q => ∫ z, φ (q • (z : V)) ∂m) := by
    refine continuous_iff_continuousAt.2 fun q₀ => ?_
    obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds q₀
    obtain ⟨k, hk, hkz⟩ := exists_compact_fib hg b₀ hK hφc
    have hcont : ContinuousOn (fun q : Q => ∫ z, φ (q • (z : V)) ∂m) K := by
      refine continuousOn_integral_of_compact_support
        (f := fun (q : Q) (z : (g ⁻¹' {b₀})) => φ (q • (z : V))) hk ?_ ?_
      · exact (hφ.comp (continuous_fst.smul
          (continuous_subtype_val.comp continuous_snd))).continuousOn
      · intro q z hq hz
        exact hvan hkz q z hq hz
    exact hcont.continuousAt hKn
  constructor
  · rintro b ⟨q, rfl⟩
    change Integrable φ (fibFam g b₀ w m (q • b₀))
    rw [fibFam_orbit w m ho.injective]
    refine Integrable.smul_measure ?_ ENNReal.coe_ne_top
    exact (integrable_map_measure hφ.aestronglyMeasurable
      (continuous_smul_fib g b₀ q).aemeasurable).2 (hint q)
  · rintro b ⟨q, rfl⟩
    refine ContinuousAt.continuousWithinAt ?_
    refine (ho.continuousAt_iff).1 ?_
    have : ((fun b => ∫ v, φ v ∂(fibFam g b₀ w m b)) ∘ fun q : Q => q • b₀) =
        fun q : Q => (w q : ℝ) * ∫ z, φ (q • (z : V)) ∂m := funext hval
    rw [this]
    exact ((NNReal.continuous_coe.comp hw).mul hG).continuousAt

theorem exists_slice_measure [T2Space V] [LocallyCompactSpace V] {g : V → X} (hg : Continuous g)
    (heq : ∀ (q : Q) (v : V), g (q • v) = q • g v) {b₀ : X}
    (ho : IsOpenEmbedding (fun q : Q => q • b₀)) (μ : Measure V) (ν : Measure X)
    [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν] [ν.IsOpenPosMeasure]
    (χ χ' : Q →* ℝ≥0) (hχ : Continuous χ) (hχ' : Continuous χ')
    (hμ : ∀ q : Q, μ.map (fun v => q • v) = χ q • μ)
    (hν : ∀ q : Q, ν.map (fun x => q • x) = χ' q • ν) :
    ∃ m : Measure (g ⁻¹' {b₀}), IsLocallyFiniteMeasure m ∧
      (μ.comap (theta (Q := Q) g b₀)).withDensity (fun p => (χ p.1 : ℝ≥0∞)) =
        ((ν.comap (fun q : Q => q • b₀)).withDensity (fun q => (χ' q : ℝ≥0∞))).prod m := by
  have hcl : IsClosed (g ⁻¹' {b₀}) := isClosed_singleton.preimage hg
  haveI : LocallyCompactSpace (g ⁻¹' {b₀}) :=
    hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  obtain ⟨hΘ, -⟩ := theta_isOpenEmbedding (Q := Q) hg heq ho
  have hΘm := hΘ.measurableEmbedding
  have hom := ho.measurableEmbedding
  have hinvmul : ∀ (c : Q →* ℝ≥0) (a : Q), ((c a⁻¹ : ℝ≥0) : ℝ≥0∞) * (c a : ℝ≥0) = 1 := by
    intro c a
    rw [← ENNReal.coe_mul, ← map_mul, inv_mul_cancel, map_one, ENNReal.coe_one]
  have hsc : ∀ (c : Q →* ℝ≥0) (a q : Q), ((c q : ℝ≥0) : ℝ≥0∞) =
      (c a⁻¹ : ℝ≥0) * (c (a * q) : ℝ≥0) := by
    intro c a q
    rw [← ENNReal.coe_mul, ← map_mul, inv_mul_cancel_left]
  haveI := comap_isLocallyFinite hΘ μ
  haveI := comap_isLocallyFinite ho ν
  set η := (ν.comap (fun q : Q => q • b₀)).withDensity (fun q => (χ' q : ℝ≥0∞)) with hη
  haveI hηf : IsLocallyFiniteMeasure η := IsLocallyFiniteMeasure.withDensity_coe hχ'
  have hηinv : η.IsMulLeftInvariant := by
    refine ⟨fun a => ?_⟩
    refine withDensity_map_of_scale (measurable_const_mul a) _ (χ' a) (χ' a⁻¹) ?_
      (measurable_coe_nnreal_ennreal.comp hχ'.measurable) (hsc χ' a) (hinvmul χ' a)
    refine comap_map_of_intertwine hom (measurable_const_mul a) (L' := fun q => a⁻¹ * q)
      (A := fun x => a • x) (A' := fun x => a⁻¹ • x) (measurable_const_smul a)
      (fun q => mul_inv_cancel_left a q) (fun x => inv_smul_smul a x)
      (fun q => mul_smul _ _ _) (fun q => mul_smul _ _ _) ν _ ?_
    rw [hν a, ENNReal.smul_def]
  have hν₀ : (ν.comap (fun q : Q => q • b₀)).IsOpenPosMeasure := by
    refine ⟨fun s hs hne h0 => ?_⟩
    rw [hom.comap_apply] at h0
    exact (ho.isOpenMap s hs).measure_pos ν (hne.image _) |>.ne' h0
  have hηpos : η.IsOpenPosMeasure := by
    have hac : (ν.comap (fun q : Q => q • b₀)) ≪ η := by
      refine withDensity_absolutelyContinuous'
        (measurable_coe_nnreal_ennreal.comp hχ'.measurable).aemeasurable
        (Filter.Eventually.of_forall fun q => ?_)
      intro h0
      have := hinvmul χ' q
      rw [ENNReal.coe_eq_zero.1 h0] at this
      simp at this
    exact hac.isOpenPosMeasure
  haveI : η.IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := inferInstance
      toIsMulLeftInvariant := hηinv
      toIsOpenPosMeasure := hηpos }
  haveI : IsLocallyFiniteMeasure
      ((μ.comap (theta (Q := Q) g b₀)).withDensity (fun p => (χ p.1 : ℝ≥0∞))) :=
    IsLocallyFiniteMeasure.withDensity_coe (f := fun p : Q × (g ⁻¹' {b₀}) => χ p.1)
      (hχ.comp continuous_fst)
  refine GlobalTheory.CompanionTheory.SW.measure_eq_haar_prod_of_left_invariant Q (g ⁻¹' {b₀}) η _ fun a => ?_
  have hLm : Measurable (fun p : Q × (g ⁻¹' {b₀}) => (a * p.1, p.2)) :=
    (continuous_const.mul continuous_fst).measurable.prodMk measurable_snd
  refine withDensity_map_of_scale hLm _ (χ a) (χ a⁻¹) ?_
    (measurable_coe_nnreal_ennreal.comp (hχ.measurable.comp measurable_fst))
    (fun p => hsc χ a p.1) (hinvmul χ a)
  refine comap_map_of_intertwine hΘm hLm (L' := fun p => (a⁻¹ * p.1, p.2))
    (A := fun x => a • x) (A' := fun x => a⁻¹ • x) (measurable_const_smul a)
    (fun p => by simp) (fun x => inv_smul_smul a x)
    (fun p => mul_smul _ _ _) (fun p => mul_smul _ _ _) μ _ ?_
  rw [hμ a, ENNReal.smul_def]

theorem lintegral_fibFam [T2Space V] {g : V → X} (hg : Continuous g)
    (heq : ∀ (q : Q) (v : V), g (q • v) = q • g v) {b₀ : X}
    (ho : IsOpenEmbedding (fun q : Q => q • b₀)) (μ : Measure V) (ν : Measure X)
    (χ χ' : Q →* ℝ≥0) (hχ : Continuous χ) (hχ' : Continuous χ')
    (m : Measure (g ⁻¹' {b₀})) [SFinite m]
    [SFinite ((ν.comap (fun q : Q => q • b₀)).withDensity (fun q => (χ' q : ℝ≥0∞)))]
    (hm : (μ.comap (theta (Q := Q) g b₀)).withDensity (fun p => (χ p.1 : ℝ≥0∞)) =
        ((ν.comap (fun q : Q => q • b₀)).withDensity (fun q => (χ' q : ℝ≥0∞))).prod m)
    {φ : V → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ v in g ⁻¹' Set.range (fun q : Q => q • b₀), φ v ∂μ =
      ∫⁻ b, ∫⁻ v, φ v ∂(fibFam g b₀ (fun q => χ' q * χ q⁻¹) m b) ∂ν := by
  obtain ⟨hΘ, hr⟩ := theta_isOpenEmbedding (Q := Q) hg heq ho
  have hΘm := hΘ.measurableEmbedding
  have hom := ho.measurableEmbedding
  have hχm : Measurable (fun q : Q => (χ q : ℝ≥0∞)) :=
    measurable_coe_nnreal_ennreal.comp hχ.measurable
  have hχim : Measurable (fun q : Q => (χ q⁻¹ : ℝ≥0∞)) :=
    measurable_coe_nnreal_ennreal.comp (hχ.comp continuous_inv).measurable
  have hχ'm : Measurable (fun q : Q => (χ' q : ℝ≥0∞)) :=
    measurable_coe_nnreal_ennreal.comp hχ'.measurable
  have hF : Measurable (fun p : Q × (g ⁻¹' {b₀}) => (χ p.1⁻¹ : ℝ≥0∞) * φ (theta g b₀ p)) :=
    (hχim.comp measurable_fst).mul (hφ.comp hΘm.measurable)

  have hleft : ∫⁻ v in g ⁻¹' Set.range (fun q : Q => q • b₀), φ v ∂μ =
      ∫⁻ q, (χ' q : ℝ≥0∞) * ∫⁻ z : (g ⁻¹' {b₀}), (χ q⁻¹ : ℝ≥0∞) * φ (q • (z : V)) ∂m
        ∂(ν.comap (fun q : Q => q • b₀)) := by
    have h1 : ∫⁻ v in g ⁻¹' Set.range (fun q : Q => q • b₀), φ v ∂μ =
        ∫⁻ p, φ (theta g b₀ p) ∂(μ.comap (theta (Q := Q) g b₀)) := by
      rw [← hr, ← hΘm.map_comap μ, lintegral_map hφ hΘm.measurable]
    have h2 : ∫⁻ p, φ (theta g b₀ p) ∂(μ.comap (theta (Q := Q) g b₀)) =
        ∫⁻ p, (χ p.1⁻¹ : ℝ≥0∞) * φ (theta g b₀ p)
          ∂((μ.comap (theta (Q := Q) g b₀)).withDensity (fun p => (χ p.1 : ℝ≥0∞))) := by
      have hd : Measurable (fun p : Q × (g ⁻¹' {b₀}) => (χ p.1 : ℝ≥0∞)) :=
        hχm.comp measurable_fst
      rw [lintegral_withDensity_eq_lintegral_mul _ hd hF]
      refine lintegral_congr fun p => ?_
      simp only [Pi.mul_apply]
      rw [← mul_assoc, ← ENNReal.coe_mul, ← map_mul, mul_inv_cancel, map_one, ENNReal.coe_one,
        one_mul]
    rw [h1, h2, hm, lintegral_prod _ hF.aemeasurable,
      lintegral_withDensity_eq_lintegral_mul _ hχ'm hF.lintegral_prod_right']
    rfl

  have hright : ∫⁻ b, ∫⁻ v, φ v ∂(fibFam g b₀ (fun q => χ' q * χ q⁻¹) m b) ∂ν =
      ∫⁻ q, ∫⁻ v, φ v ∂(fibFam g b₀ (fun q => χ' q * χ q⁻¹) m (q • b₀))
        ∂(ν.comap (fun q : Q => q • b₀)) := by
    have hB : MeasurableSet (Set.range (fun q : Q => q • b₀)) := ho.isOpen_range.measurableSet
    have hoff : ∫⁻ b in (Set.range (fun q : Q => q • b₀))ᶜ,
        ∫⁻ v, φ v ∂(fibFam g b₀ (fun q => χ' q * χ q⁻¹) m b) ∂ν = 0 := by
      rw [setLIntegral_congr_fun (g := fun _ => 0) hB.compl]
      · simp
      · intro b hb
        simp only
        rw [fibFam_off _ m hb]
        simp
    have hmap := hom.lintegral_map (μ := ν.comap (fun q : Q => q • b₀))
      (fun b => ∫⁻ v, φ v ∂(fibFam g b₀ (fun q => χ' q * χ q⁻¹) m b))
    rw [hom.map_comap] at hmap
    rw [← lintegral_add_compl _ hB, hoff, add_zero]
    exact hmap
  rw [hleft, hright]
  refine lintegral_congr fun q => ?_
  have hc : ∫⁻ z : (g ⁻¹' {b₀}), (χ q⁻¹ : ℝ≥0∞) * φ (q • (z : V)) ∂m =
      (χ q⁻¹ : ℝ≥0∞) * ∫⁻ z : (g ⁻¹' {b₀}), φ (q • (z : V)) ∂m :=
    lintegral_const_mul _ (hφ.comp (continuous_smul_fib g b₀ q).measurable)
  rw [fibFam_orbit _ m ho.injective, lintegral_smul_measure,
    lintegral_map hφ (continuous_smul_fib g b₀ q).measurable, hc, smul_eq_mul,
    ENNReal.coe_mul, mul_assoc]

end Core

theorem exists_isFibreFamily_openOrbit : ∀ (V X Y : Type) [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X) [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν] [ν.IsOpenPosMeasure] (f : V → Y) (g : V → X) (ι : X → Y), Function.Injective ι → Continuous g → (∀ v, f v = ι (g v)) → ∀ (Q : Type) [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [LocallyCompactSpace Q] [SecondCountableTopology Q] [T2Space Q] [MulAction Q V] [ContinuousSMul Q V] [MulAction Q X] [ContinuousSMul Q X], (∀ (q : Q) (v : V), g (q • v) = q • g v) → ∀ (χ χ' : Q →* ℝ≥0), Continuous χ → Continuous χ' → (∀ q : Q, μ.map (fun v => q • v) = χ q • μ) → (∀ q : Q, ν.map (fun x => q • x) = χ' q • ν) → ∀ b₀ : X, IsOpenEmbedding (fun q : Q => q • b₀) → ∃ fib : X → Measure V, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' (Set.range fun q : Q => q • b₀)) ν (Set.range fun q : Q => q • b₀) fib := by
  intro V X Y _ _ _ _ _ _ _ _ _ _ _ _ μ ν _ _ _ f g ι hι hg hf Q _ _ _ _ _ _ _ _ _ _ heq χ χ' hχ hχ'
    hμ hν b₀ ho
  letI : MeasurableSpace Q := borel Q
  haveI : BorelSpace Q := ⟨rfl⟩
  obtain ⟨m, hmf, hm⟩ := exists_slice_measure hg heq ho μ ν χ χ' hχ hχ' hμ hν
  have hcl : IsClosed (g ⁻¹' {b₀}) := isClosed_singleton.preimage hg
  haveI := comap_isLocallyFinite ho ν
  haveI : IsLocallyFiniteMeasure
      ((ν.comap (fun q : Q => q • b₀)).withDensity (fun q => (χ' q : ℝ≥0∞))) :=
    IsLocallyFiniteMeasure.withDensity_coe hχ'
  have hw : Continuous (fun q : Q => χ' q * χ q⁻¹) := hχ'.mul (hχ.comp continuous_inv)
  refine ⟨fibFam g b₀ (fun q => χ' q * χ q⁻¹) m, fibFam_support hι hg hf heq ho _ m, ?_, ?_⟩
  · exact fun φ hφ => lintegral_fibFam hg heq ho μ ν χ χ' hχ hχ' m hm hφ
  · exact fun φ hφ hφc _ => integrable_and_continuous hg ho hw m hφ hφc

end GlobalTheory.CompanionTheory.SW.Slice
