import Mathlib
import Formalism.UnipotentAdelicQuotients.SWXSDefs
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.DisintegrationDensityContinuousStatement
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.SW.FibreDensity

variable {V X Y : Type}
  [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V]
  [MeasurableSpace V] [BorelSpace V]
  [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]
  {μ : Measure V} {ν : Measure X} {f : V → Y} {g : V → X} {ι : X → Y} {B : Set X}
  {fib : X → Measure V}

lemma ae_eq_point (hι : Function.Injective ι) (hf : ∀ v, f v = ι (g v))
    (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B) ν B fib) (b : X) :
    ∀ᵐ v ∂(fib b), g v = b := by
  have h1 : ∀ᵐ v ∂(fib b), v ∈ f ⁻¹' {ι b} ∩ g ⁻¹' B := by
    rw [ae_iff]; exact h.1 b
  filter_upwards [h1] with v hv
  exact hι ((hf v).symm.trans hv.1)

lemma lintegral_preimage (hι : Function.Injective ι) (hf : ∀ v, f v = ι (g v))
    (hg : Continuous g)
    (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B) ν B fib)
    {S : Set X} (hS : IsCompact S) (hSB : S ⊆ B) {u : V → ℝ≥0∞} (hu : Measurable u) :
    ∫⁻ v in g ⁻¹' S, u v ∂μ = ∫⁻ b in S, ∫⁻ v, u v ∂(fib b) ∂ν := by
  have hSm : MeasurableSet S := hS.isClosed.measurableSet
  have hgS : MeasurableSet (g ⁻¹' S) := hg.measurable hSm
  have key := h.2.1 ((g ⁻¹' S).indicator u) (hu.indicator hgS)
  have hpt : ∀ b, ∫⁻ v, (g ⁻¹' S).indicator u v ∂(fib b)
      = S.indicator (fun b => ∫⁻ v, u v ∂(fib b)) b := by
    intro b
    by_cases hb : b ∈ S
    · rw [Set.indicator_of_mem hb]
      refine lintegral_congr_ae ?_
      filter_upwards [ae_eq_point hι hf h b] with v hv
      exact Set.indicator_of_mem (show v ∈ g ⁻¹' S by simpa [hv] using hb) u
    · rw [Set.indicator_of_notMem hb]
      have : (fun v => (g ⁻¹' S).indicator u v) =ᵐ[fib b] fun _ => 0 := by
        filter_upwards [ae_eq_point hι hf h b] with v hv
        exact Set.indicator_of_notMem (show v ∉ g ⁻¹' S by simpa [hv] using hb) u
      rw [lintegral_congr_ae this]; simp
  simp_rw [hpt] at key
  rw [lintegral_indicator hSm, setLIntegral_indicator hgS] at key
  have hsub : g ⁻¹' S ∩ g ⁻¹' B = g ⁻¹' S :=
    Set.inter_eq_left.mpr (Set.preimage_mono hSB)
  rwa [hsub] at key

lemma integral_preimage_nonneg [IsLocallyFiniteMeasure ν] [IsLocallyFiniteMeasure μ]
    (hfin : ∀ b, IsLocallyFiniteMeasure (fib b))
    (hι : Function.Injective ι) (hf : ∀ v, f v = ι (g v)) (hg : Continuous g)
    (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B) ν B fib)
    {S : Set X} (hS : IsCompact S) (hSB : S ⊆ B) {u : V → ℝ} (hc : Continuous u)
    (hs : HasCompactSupport u) (hsupp : tsupport u ⊆ g ⁻¹' B) (h0 : ∀ v, 0 ≤ u v) :
    ∫ v in g ⁻¹' S, u v ∂μ = ∫ b in S, ∫ v, u v ∂(fib b) ∂ν := by
  have hSm : MeasurableSet S := hS.isClosed.measurableSet
  have hcont := (h.2.2 u hc hs hsupp).2
  have hm : AEStronglyMeasurable (fun b => ∫ v, u v ∂(fib b)) (ν.restrict S) :=
    (hcont.mono hSB).aestronglyMeasurable hSm
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall h0)
      hc.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun b => integral_nonneg h0) hm,
    lintegral_preimage hι hf hg h hS hSB (hc.measurable.ennreal_ofReal)]
  congr 1
  refine lintegral_congr fun b => ?_
  haveI := hfin b
  exact (ofReal_integral_eq_lintegral_ofReal (hc.integrable_of_hasCompactSupport hs)
    (Filter.Eventually.of_forall h0)).symm

lemma integral_preimage_real [IsLocallyFiniteMeasure ν] [IsLocallyFiniteMeasure μ]
    (hfin : ∀ b, IsLocallyFiniteMeasure (fib b))
    (hι : Function.Injective ι) (hf : ∀ v, f v = ι (g v)) (hg : Continuous g)
    (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B) ν B fib)
    {S : Set X} (hS : IsCompact S) (hSB : S ⊆ B) {u : V → ℝ} (hc : Continuous u)
    (hs : HasCompactSupport u) (hsupp : tsupport u ⊆ g ⁻¹' B) :
    ∫ v in g ⁻¹' S, u v ∂μ = ∫ b in S, ∫ v, u v ∂(fib b) ∂ν := by
  set p : V → ℝ := fun v => max (u v) 0 with hp
  set q : V → ℝ := fun v => max (-u v) 0 with hq
  have hpc : Continuous p := hc.max continuous_const
  have hqc : Continuous q := hc.neg.max continuous_const
  have hps : Function.support p ⊆ Function.support u := by
    intro v hv hv0
    exact hv (by simp [hp, show u v = 0 from hv0])
  have hqs : Function.support q ⊆ Function.support u := by
    intro v hv hv0
    exact hv (by simp [hq, show u v = 0 from hv0])
  have hpK : HasCompactSupport p := hs.mono hps
  have hqK : HasCompactSupport q := hs.mono hqs
  have hpt : tsupport p ⊆ g ⁻¹' B := (closure_mono hps).trans hsupp
  have hqt : tsupport q ⊆ g ⁻¹' B := (closure_mono hqs).trans hsupp
  have hsplit : ∀ v, u v = p v - q v := fun v => by
    simp only [hp, hq]
    rcases le_total (u v) 0 with h1 | h1
    · rw [max_eq_right h1, max_eq_left (by linarith)]; ring
    · rw [max_eq_left h1, max_eq_right (by linarith)]; ring
  have hP := integral_preimage_nonneg hfin hι hf hg h hS hSB hpc hpK hpt
    (fun v => le_max_right _ _)
  have hQ := integral_preimage_nonneg hfin hι hf hg h hS hSB hqc hqK hqt
    (fun v => le_max_right _ _)
  have hIp : Integrable p μ := hpc.integrable_of_hasCompactSupport hpK
  have hIq : Integrable q μ := hqc.integrable_of_hasCompactSupport hqK
  have hGp : IntegrableOn (fun b => ∫ v, p v ∂(fib b)) S ν :=
    ((h.2.2 p hpc hpK hpt).2.mono hSB).integrableOn_compact hS
  have hGq : IntegrableOn (fun b => ∫ v, q v ∂(fib b)) S ν :=
    ((h.2.2 q hqc hqK hqt).2.mono hSB).integrableOn_compact hS
  have hb : ∀ b, ∫ v, u v ∂(fib b) = ∫ v, p v ∂(fib b) - ∫ v, q v ∂(fib b) := fun b => by
    haveI := hfin b
    simp_rw [hsplit]
    exact integral_sub (hpc.integrable_of_hasCompactSupport hpK)
      (hqc.integrable_of_hasCompactSupport hqK)
  simp_rw [hb]
  rw [integral_sub hGp hGq, ← hP, ← hQ, ← integral_sub hIp.integrableOn hIq.integrableOn]
  simp_rw [hsplit]

lemma integral_fib_eq (hfin : ∀ b, IsLocallyFiniteMeasure (fib b)) {ψ : V → ℂ}
    (hc : Continuous ψ) (hs : HasCompactSupport ψ) (b : X) :
    ∫ v, ψ v ∂(fib b) = ((∫ v, (ψ v).re ∂(fib b) : ℝ) : ℂ)
      + ((∫ v, (ψ v).im ∂(fib b) : ℝ) : ℂ) * Complex.I := by
  haveI := hfin b
  exact (integral_re_add_im (𝕜 := ℂ) (hc.integrable_of_hasCompactSupport hs)).symm

lemma re_facts {ψ : V → ℂ} (hc : Continuous ψ) (hs : HasCompactSupport ψ)
    {U : Set V} (hsupp : tsupport ψ ⊆ U) :
    Continuous (fun v => (ψ v).re) ∧ HasCompactSupport (fun v => (ψ v).re) ∧
      tsupport (fun v => (ψ v).re) ⊆ U := by
  have hsub : Function.support (fun v => (ψ v).re) ⊆ Function.support ψ := by
    intro v hv hv0
    exact hv (by simp [show ψ v = 0 from hv0])
  exact ⟨Complex.continuous_re.comp hc, hs.mono hsub, (closure_mono hsub).trans hsupp⟩

lemma im_facts {ψ : V → ℂ} (hc : Continuous ψ) (hs : HasCompactSupport ψ)
    {U : Set V} (hsupp : tsupport ψ ⊆ U) :
    Continuous (fun v => (ψ v).im) ∧ HasCompactSupport (fun v => (ψ v).im) ∧
      tsupport (fun v => (ψ v).im) ⊆ U := by
  have hsub : Function.support (fun v => (ψ v).im) ⊆ Function.support ψ := by
    intro v hv hv0
    exact hv (by simp [show ψ v = 0 from hv0])
  exact ⟨Complex.continuous_im.comp hc, hs.mono hsub, (closure_mono hsub).trans hsupp⟩

lemma continuousOn_fib (hfin : ∀ b, IsLocallyFiniteMeasure (fib b))
    (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B) ν B fib)
    {ψ : V → ℂ} (hc : Continuous ψ) (hs : HasCompactSupport ψ)
    (hsupp : tsupport ψ ⊆ g ⁻¹' B) :
    ContinuousOn (fun b => ∫ v, ψ v ∂(fib b)) B := by
  obtain ⟨r1, r2, r3⟩ := re_facts hc hs hsupp
  obtain ⟨i1, i2, i3⟩ := im_facts hc hs hsupp
  have hre := (h.2.2 _ r1 r2 r3).2
  have him := (h.2.2 _ i1 i2 i3).2
  simp_rw [integral_fib_eq hfin hc hs]
  exact (Complex.continuous_ofReal.comp_continuousOn hre).add
    ((Complex.continuous_ofReal.comp_continuousOn him).mul continuousOn_const)

lemma integral_preimage_complex [IsLocallyFiniteMeasure ν] [IsLocallyFiniteMeasure μ]
    (hfin : ∀ b, IsLocallyFiniteMeasure (fib b))
    (hι : Function.Injective ι) (hf : ∀ v, f v = ι (g v)) (hg : Continuous g)
    (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B) ν B fib)
    {S : Set X} (hS : IsCompact S) (hSB : S ⊆ B) {ψ : V → ℂ} (hc : Continuous ψ)
    (hs : HasCompactSupport ψ) (hsupp : tsupport ψ ⊆ g ⁻¹' B) :
    ∫ v in g ⁻¹' S, ψ v ∂μ = ∫ b in S, ∫ v, ψ v ∂(fib b) ∂ν := by
  obtain ⟨r1, r2, r3⟩ := re_facts hc hs hsupp
  obtain ⟨i1, i2, i3⟩ := im_facts hc hs hsupp
  have hR := integral_preimage_real hfin hι hf hg h hS hSB r1 r2 r3
  have hI := integral_preimage_real hfin hι hf hg h hS hSB i1 i2 i3
  have hIv : IntegrableOn ψ (g ⁻¹' S) μ := (hc.integrable_of_hasCompactSupport hs).integrableOn
  have hIb : IntegrableOn (fun b => ∫ v, ψ v ∂(fib b)) S ν :=
    ((continuousOn_fib hfin h hc hs hsupp).mono hSB).integrableOn_compact hS
  have hfre : ∀ b, ∫ v, (ψ v).re ∂(fib b) = (∫ v, ψ v ∂(fib b)).re := fun b => by
    haveI := hfin b
    exact integral_re (𝕜 := ℂ) (hc.integrable_of_hasCompactSupport hs)
  have hfim : ∀ b, ∫ v, (ψ v).im ∂(fib b) = (∫ v, ψ v ∂(fib b)).im := fun b => by
    haveI := hfin b
    exact integral_im (𝕜 := ℂ) (hc.integrable_of_hasCompactSupport hs)
  apply Complex.ext
  · have e1 : ∫ v in g ⁻¹' S, (ψ v).re ∂μ = (∫ v in g ⁻¹' S, ψ v ∂μ).re :=
      integral_re (𝕜 := ℂ) hIv
    have e2 : ∫ b in S, (∫ v, ψ v ∂(fib b)).re ∂ν = (∫ b in S, ∫ v, ψ v ∂(fib b) ∂ν).re :=
      integral_re (𝕜 := ℂ) hIb
    rw [← e1, ← e2, hR]
    simp_rw [hfre]
  · have e1 : ∫ v in g ⁻¹' S, (ψ v).im ∂μ = (∫ v in g ⁻¹' S, ψ v ∂μ).im :=
      integral_im (𝕜 := ℂ) hIv
    have e2 : ∫ b in S, (∫ v, ψ v ∂(fib b)).im ∂ν = (∫ b in S, ∫ v, ψ v ∂(fib b) ∂ν).im :=
      integral_im (𝕜 := ℂ) hIb
    rw [← e1, ← e2, hI]
    simp_rw [hfim]

lemma exists_cutoff (hg : Continuous g) (hB : IsOpen B) {K : Set X} (hK : IsCompact K)
    (hKB : K ⊆ B) {φ : V → ℂ} (hc : Continuous φ) (hs : HasCompactSupport φ) :
    ∃ ψ : V → ℂ, Continuous ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ g ⁻¹' B ∧
      ∀ v, g v ∈ K → ψ v = φ v := by
  obtain ⟨χ, h1, -, hsupp, -⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hK hB hKB
  refine ⟨fun v => (χ (g v) : ℂ) * φ v, ?_, ?_, ?_, ?_⟩
  · exact (Complex.continuous_ofReal.comp (χ.continuous.comp hg)).mul hc
  · exact hs.mono (fun v hv hv0 => hv (by simp [show φ v = 0 from hv0]))
  · have hsub : Function.support (fun v => (χ (g v) : ℂ) * φ v) ⊆ g ⁻¹' tsupport χ := by
      intro v hv
      apply subset_tsupport
      intro h0
      exact hv (by simp [show χ (g v) = 0 from h0])
    exact (closure_minimal hsub ((isClosed_tsupport _).preimage hg)).trans
      (Set.preimage_mono hsupp)
  · intro v hv
    have : χ (g v) = 1 := h1 hv
    simp [this]

theorem isContDensityOn_fibreIntegral : ∀ (V X Y : Type) [TopologicalSpace V]
    [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V]
    [BorelSpace V] [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X]
    [T2Space X] [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X)
    [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν] [ν.IsOpenPosMeasure] (f : V → Y)
    (g : V → X) (ι : X → Y), Function.Injective ι → Continuous g → (∀ v, f v = ι (g v)) →
    ∀ (B : Set X), IsOpen B → ∀ fib : X → Measure V,
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B) ν B fib →
    ∀ φ : V → ℂ, Continuous φ → HasCompactSupport φ →
    HeckeCharacterZeroLocus.SiegelWeilU.IsContDensityOn μ f ι ν B φ (fun b => ∫ v, φ v ∂(fib b)) ∧
      ∀ b, Integrable φ (fib b) := by
  intro V X Y _ _ _ _ _ _ _ _ _ _ _ _ μ ν _ _ _ f g ι hι hg hf B hB fib h φ hc hs
  have hfin := (GlobalTheory.T.fibre_family_locallyFinite_measurable_bdd_on_compact V X Y μ ν f g ι hι hg hf B hB fib h).1
  have hcongr : ∀ {ψ : V → ℂ} {K : Set X}, (∀ v, g v ∈ K → ψ v = φ v) → ∀ b ∈ K,
      ∫ v, ψ v ∂(fib b) = ∫ v, φ v ∂(fib b) := by
    intro ψ K hψ b hb
    refine integral_congr_ae ?_
    filter_upwards [ae_eq_point hι hf h b] with v hv
    exact hψ v (hv ▸ hb)
  refine ⟨⟨?_, ?_⟩, fun b => ?_⟩
  · intro b₀ hb₀
    obtain ⟨K, hKn, hKB, hK⟩ := local_compact_nhds (hB.mem_nhds hb₀)
    obtain ⟨ψ, c1, c2, c3, c4⟩ := exists_cutoff hg hB hK hKB hc hs
    have hat : ContinuousAt (fun b => ∫ v, ψ v ∂(fib b)) b₀ :=
      (continuousOn_fib hfin h c1 c2 c3).continuousAt (hB.mem_nhds hb₀)
    refine (hat.congr ?_).continuousWithinAt
    filter_upwards [hKn] with b hb
    exact hcongr c4 b hb
  · intro S hS hSB
    have hpre : f ⁻¹' (ι '' S) = g ⁻¹' S := by
      ext v
      simp only [Set.mem_preimage, Set.mem_image, hf]
      constructor
      · rintro ⟨x, hx, hxv⟩
        exact hι hxv ▸ hx
      · exact fun hv => ⟨g v, hv, rfl⟩
    have hSm : MeasurableSet S := hS.isClosed.measurableSet
    obtain ⟨ψ, c1, c2, c3, c4⟩ := exists_cutoff hg hB hS hSB hc hs
    rw [hpre]
    calc ∫ v in g ⁻¹' S, φ v ∂μ = ∫ v in g ⁻¹' S, ψ v ∂μ :=
          setIntegral_congr_fun (hg.measurable hSm) (fun v hv => (c4 v hv).symm)
      _ = ∫ b in S, ∫ v, ψ v ∂(fib b) ∂ν :=
          integral_preimage_complex hfin hι hf hg h hS hSB c1 c2 c3
      _ = ∫ b in S, ∫ v, φ v ∂(fib b) ∂ν :=
          setIntegral_congr_fun hSm (fun b hb => hcongr c4 b hb)
  · haveI := hfin b
    exact hc.integrable_of_hasCompactSupport hs

end GlobalTheory.CompanionTheory.SW.FibreDensity
