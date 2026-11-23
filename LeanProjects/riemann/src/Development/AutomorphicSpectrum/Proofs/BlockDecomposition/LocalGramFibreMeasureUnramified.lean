import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitHermOfDet
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRing
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianMatricesLocallyCompactBorel
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FibreMassEq
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensTop
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Coef.AvgV

theorem ae_lift_eq {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [TopologicalSpace X] [MeasurableSpace X]
    {μ : Measure V} {ν : Measure X} {q : V → Y} {ι : X → Y} {W : Set V} {B : Set X} {fib : X → Measure V}
    (h : IsFibreFamily μ q ι W ν B fib) {g : V → X} (hg : ∀ x, q x = ι (g x)) (hι : Function.Injective ι)
    (b : X) : ∀ᵐ x ∂(fib b), g x = b := by
  refine measure_mono_null ?_ (h.1 b)
  intro x hx hx'
  exact hx (hι ((hg x).symm.trans hx'.1))

theorem fibre_mass_on {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [TopologicalSpace X]
    [MeasurableSpace X] {μ : Measure V} {ν : Measure X} {q : V → Y} {ι : X → Y} {W : Set V} {B : Set X}
    {fib : X → Measure V} (h : IsFibreFamily μ q ι W ν B fib) {g : V → X} (hg : ∀ x, q x = ι (g x))
    (hι : Function.Injective ι) (hgm : Measurable g) {A : Set V} {S : Set X} (hA : MeasurableSet A)
    (hS : MeasurableSet S) (hW : A ∩ g ⁻¹' S ⊆ W) :
    μ (A ∩ g ⁻¹' S) = ∫⁻ s in S, fib s A ∂ν := by
  have hT : MeasurableSet (A ∩ g ⁻¹' S) := hA.inter (hgm hS)
  have e := h.2.1 ((A ∩ g ⁻¹' S).indicator 1) (measurable_one.indicator hT)
  simp only [lintegral_indicator_one hT] at e
  rw [Measure.restrict_apply hT, Set.inter_eq_left.2 hW] at e
  rw [e, ← lintegral_indicator hS]
  refine lintegral_congr fun b => ?_
  have hae := ae_lift_eq h hg hι b
  by_cases hb : b ∈ S
  · rw [Set.indicator_of_mem hb]
    refine measure_congr ?_
    filter_upwards [hae] with x hx
    refine propext ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
    show g x ∈ S
    rwa [hx]
  · rw [Set.indicator_of_notMem hb]
    refine measure_mono_null (t := {x | ¬ g x = b}) ?_ hae
    intro x hx hxb
    apply hb
    rw [← hxb]
    exact hx.2

theorem avg_gen {V X Y : Type} {_ : TopologicalSpace V} {_ : MeasurableSpace V} {_ : TopologicalSpace X}
    {_ : MeasurableSpace X} {_ : AddCommGroup X} {μ : Measure V} {ν : Measure X} {q : V → Y} {ι : X → Y}
    {W : Set V} {B : Set X} {fib : X → Measure V} (h : IsFibreFamily μ q ι W ν B fib) {g : V → X}
    (hg : ∀ x, q x = ι (g x)) (hι : Function.Injective ι) (hgc : Continuous g) (hV2 : T2Space V)
    (hVb : BorelSpace V) (hX2 : T2Space X) (hXb : BorelSpace X) (hXg : IsTopologicalAddGroup X)
    (hXl : LocallyCompactSpace X) (hXs : SecondCountableTopology X) (hμ : IsFiniteMeasureOnCompacts μ)
    (hν : ν.IsAddHaarMeasure) (hB : IsOpen B) (hWB : ∀ x, g x ∈ B → x ∈ W) {c : X} (hc : c ∈ B) {A : Set V}
    (hAc : IsCompact A) (hAo : IsOpen A) {U : ℕ → Set X} (hU : ∀ k, IsCompact (U k) ∧ IsOpen (U k) ∧ (0 : X) ∈ U k)
    (hUt : Filter.Tendsto U Filter.atTop (nhds (0 : X)).smallSets) :
    (∀ k, MeasurableSet (A ∩ {x | c - g x ∈ U k}) ∧ μ (A ∩ {x | c - g x ∈ U k}) ≠ ⊤) ∧
      Filter.Tendsto (fun k => (μ (A ∩ {x | c - g x ∈ U k})).toReal / (ν (U k)).toReal) Filter.atTop
        (nhds (fib c A).toReal) := by
  haveI : ν.IsNegInvariant := Measure.IsAddHaarMeasure.isNegInvariant_of_regular _
  have hBc := hB.mem_nhds hc

  let S : ℕ → Set X := fun k => {s | c - s ∈ U k}
  have hSo : ∀ k, IsOpen (S k) := fun k => (hU k).2.1.preimage (continuous_const.sub continuous_id)
  have hSm : ∀ k, MeasurableSet (S k) := fun k => (hSo k).measurableSet
  have hSc : ∀ k, c ∈ S k := fun k => by
    show c - c ∈ U k
    rw [sub_self]
    exact (hU k).2.2
  have hSU : ∀ k, ν (S k) = ν (U k) := fun k =>
    (Measure.measurePreserving_sub_left _ c).measure_preimage (hU k).2.1.measurableSet.nullMeasurableSet
  have hpos : ∀ k, ν (S k) ≠ 0 := fun k => (hSo k).measure_ne_zero _ ⟨c, hSc k⟩
  have htop : ∀ k, ν (S k) ≠ ⊤ := fun k => by
    rw [hSU]
    exact (hU k).1.measure_lt_top.ne
  have hl : Filter.Tendsto S Filter.atTop (nhds c).smallSets := by
    rw [Filter.tendsto_smallSets_iff]
    intro t ht
    have hcont : Filter.Tendsto (fun u : X => c - u) (nhds 0) (nhds c) := by
      have : Continuous fun u : X => c - u := continuous_const.sub continuous_id
      simpa using this.tendsto 0
    have h0 := (Filter.tendsto_smallSets_iff.1 hUt) _ (hcont ht)
    filter_upwards [h0] with k hk s hs
    have := hk (show c - s ∈ U k from hs)
    simpa using this

  obtain ⟨k0, hk0⟩ := (hl.eventually (Filter.eventually_smallSets_subset.2 hBc)).exists
  have hNc : IsCompact (S k0) := (Homeomorph.subLeft c).isCompact_preimage.2 (hU k0).1
  let A' : Set V := A ∩ g ⁻¹' S k0
  have hA'c : IsCompact A' := hAc.inter_right (hNc.isClosed.preimage hgc)
  have hA'o : IsOpen A' := hAo.inter ((hSo k0).preimage hgc)
  have hA'm : MeasurableSet A' := hA'o.measurableSet
  have hA'W : A' ⊆ W := fun x hx => hWB x (hk0 hx.2)

  let φ : V → ℝ := A'.indicator fun _ => 1
  have hφc : Continuous φ := by
    refine continuous_indicator ?_ continuous_const.continuousOn
    simp [hA'o.frontier_eq, hA'c.isClosed.closure_eq]
  have hφs : HasCompactSupport φ := by
    refine HasCompactSupport.intro hA'c fun x hx => ?_
    exact Set.indicator_of_notMem hx _
  have hts : tsupport φ ⊆ W := by
    refine subset_trans (closure_minimal (fun x hx => ?_) hA'c.isClosed) hA'W
    by_contra h
    exact hx (Set.indicator_of_notMem h _)
  obtain ⟨hI, hC⟩ := h.2.2 φ hφc hφs hts
  have hint : ∀ s, ∫ x, φ x ∂(fib s) = (fib s A').toReal := fun s => by
    simp [φ, integral_indicator hA'm, Measure.real]
  have hG : ContinuousAt (fun s => (fib s A').toReal) c := by
    have h := hC.continuousAt hBc
    simpa only [hint] using h
  have hfin : ∀ᶠ s in nhds c, fib s A' ≠ ⊤ := by
    filter_upwards [hBc] with s hs
    have h := hI s hs
    rw [integrable_indicator_iff hA'm] at h
    rcases (integrableOn_const_iff (C := (1 : ℝ)) (by simp)).1 h with h | h
    · simp at h
    · exact h.ne
  have hcv : fib c A' = fib c A := by
    refine measure_congr ?_
    filter_upwards [ae_lift_eq h hg hι c] with x hx
    refine propext ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
    show g x ∈ S k0
    rw [hx]
    exact hSc k0
  refine ⟨fun k => ?_, ?_⟩
  · have hO : IsOpen (A ∩ {x | c - g x ∈ U k}) := hAo.inter ((hSo k).preimage hgc)
    exact ⟨hO.measurableSet, ne_top_of_le_ne_top hAc.measure_lt_top.ne (measure_mono Set.inter_subset_left)⟩
  · have key := GlobalTheory.CompanionTheory.Hypotheses₂.OneV.AvgV.tendsto_mean ν (fun s => fib s A') c hG hfin S hSm hl hpos htop
    simp only [hcv] at key
    refine key.congr' ?_
    filter_upwards [hl.eventually (Filter.eventually_smallSets_subset.2 ((hSo k0).mem_nhds (hSc k0)))] with k hk
    have e : A ∩ {x | c - g x ∈ U k} = A' ∩ g ⁻¹' S k := by
      ext x
      exact ⟨fun h => ⟨⟨h.1, hk h.2⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
    rw [hSU k, e, fibre_mass_on h hg hι hgc.measurable hA'm (hSm k) (fun x hx => hA'W hx.1)]

end GlobalTheory.CompanionTheory.SiegelND.Coef.AvgV

theorem GlobalTheory.CompanionTheory.SiegelND.Coef.avgV_tendsto : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ), 2 * n < M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lv : Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdV v lv → ∀ mv : HermR (Fv F v) σ n → Measure (Fin n → Fin M → Fv F v ⊗[F] E), GlobalTheory.CompanionTheory.SW.IsGramFib (Fv F v) σ J n (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n) mv → ∀ c : HermR (Fv F v) σ n, IsUnit (c : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)).det → ∀ A : Set (Fin n → Fin M → Fv F v ⊗[F] E), IsCompact A → IsOpen A → ∀ U : ℕ → Set (HermR (Fv F v) σ n), (∀ k, IsCompact (U k) ∧ IsOpen (U k) ∧ (0 : HermR (Fv F v) σ n) ∈ U k) → Filter.Tendsto U Filter.atTop (nhds (0 : HermR (Fv F v) σ n)).smallSets → (∀ k, MeasurableSet (A ∩ {X | c - gramH hCM hJ (Fv F v) X ∈ U k}) ∧ GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M (A ∩ {X | c - gramH hCM hJ (Fv F v) X ∈ U k}) ≠ ⊤) ∧ Filter.Tendsto (fun k => (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M (A ∩ {X | c - gramH hCM hJ (Fv F v) X ∈ U k})).toReal / (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n (U k)).toReal) Filter.atTop (nhds (mv c A).toReal) := by
  intro F E _ _ _ _ _ σ hCM M J hJ n _ d b v lv hlv mv hmv c hc A hAc hAo U hU hUt
  obtain ⟨r1, r2, r3, r4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI := r1
  haveI := r2
  haveI := r3
  haveI := r4
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  obtain ⟨a1, a2, a3, a4, -, -, -, a8, -, a10⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Fv F v)
  haveI := a1
  haveI := a2
  haveI := a3
  haveI := a4
  obtain ⟨-, hW, hH⟩ := GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hCM (Fv F v) d b lv hlv.1
  obtain ⟨e1, e2, e3, e4, -⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hCM (Fv F v) n
  have hgc : Continuous (gramH hCM hJ (Fv F v) : (Fin n → Fin M → Fv F v ⊗[F] E) → HermR (Fv F v) σ n) :=
    Continuous.subtype_mk (a10 n M J) _
  have hUo : IsOpen {r : Fv F v | IsUnit r} := by
    have : {r : Fv F v | IsUnit r} = {r | r ≠ 0} := by
      ext r
      simp [isUnit_iff_ne_zero]
    rw [this]
    exact isOpen_ne
  have hB : IsOpen {S : HermR (Fv F v) σ n | IsUnit (S : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)).det} :=
    PI.VolStabS.isOpen_unitHerm (Fv F v) hUo σ n
  exact AvgV.avg_gen (q := gramR (Fv F v) σ J) (ι := Subtype.val) (g := gramH hCM hJ (Fv F v)) hmv
    (fun _ => rfl) Subtype.val_injective hgc inferInstance (a8 n M) e3 e4 inferInstance e1 e2
    (hW n M).toIsFiniteMeasureOnCompacts (hH n) hB (fun _ h => h) hc hAc hAo hU hUt
