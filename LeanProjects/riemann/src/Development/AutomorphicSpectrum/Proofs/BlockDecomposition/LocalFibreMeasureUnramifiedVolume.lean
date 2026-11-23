import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EMatMulNegCol
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFibreMeasureUnramifiedFormulaStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FibreMassEq
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianMatricesLocallyCompactBorel
open scoped Matrix NNReal ENNReal TensorProduct
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.AvgFree MeasureTheory

namespace GlobalTheory.CompanionTheory.AvgFree.Lim

theorem tendsto_of_squeeze (a : ℕ → ℝ) (b : ℕ → ℕ → ℝ) (t e : ℕ → ℝ) (L : ℝ)
    (he : Filter.Tendsto e Filter.atTop (nhds 0)) (ht : Filter.Tendsto t Filter.atTop (nhds L))
    (hb : ∀ j, Filter.Tendsto (b j) Filter.atTop (nhds (t j)))
    (h1 : ∀ j k, b j k ≤ a k) (h2 : ∀ j k, a k ≤ b j k + e j) :
    Filter.Tendsto a Filter.atTop (nhds L) := by
  rw [Metric.tendsto_nhds]
  intro δ hδ
  have hδ3 : 0 < δ / 3 := by positivity
  have e1 := he.eventually (Metric.ball_mem_nhds _ hδ3)
  have e2 := ht.eventually (Metric.ball_mem_nhds _ hδ3)
  obtain ⟨j, hj1, hj2⟩ := (e1.and e2).exists
  have e3 := (hb j).eventually (Metric.ball_mem_nhds _ hδ3)
  filter_upwards [e3] with k hk
  rw [Real.dist_eq] at hj1 hj2 hk
  have p1 := abs_lt.1 hj1
  have p2 := abs_lt.1 hj2
  have p3 := abs_lt.1 hk
  have p4 := h1 j k
  have p5 := h2 j k
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

theorem le_of_forall_mean_le {H : Type} [TopologicalSpace H] [LocallyCompactSpace H] [MeasurableSpace H]
    [OpensMeasurableSpace H] (ν : Measure H) [ν.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts ν]
    (G : H → ℝ≥0∞) (hGc : Continuous fun y => (G y).toReal) (hGf : ∀ y, G y ≠ ⊤) (D : ℝ≥0)
    (hD : ∀ Y, MeasurableSet Y → ∫⁻ y in Y, G y ∂ν ≤ D * ν Y) (c : H) : G c ≤ D := by
  by_contra hlt
  have hlt' : (D : ℝ≥0∞) < G c := not_le.1 hlt
  have hr : (D : ℝ) < (G c).toReal := by
    have := (ENNReal.toReal_lt_toReal ENNReal.coe_ne_top (hGf c)).2 hlt'
    simpa using this
  obtain ⟨r, hr1, hr2⟩ := exists_between hr
  have hO : IsOpen {y | r < (G y).toReal} := isOpen_lt continuous_const hGc
  obtain ⟨K, hK, hcK, hKO⟩ := exists_compact_subset hO hr2
  have hYm : MeasurableSet (interior K) := isOpen_interior.measurableSet
  have hpos : ν (interior K) ≠ 0 := isOpen_interior.measure_ne_zero ν ⟨c, hcK⟩
  have hfin : ν (interior K) ≠ ⊤ := ne_top_of_le_ne_top hK.measure_lt_top.ne (measure_mono interior_subset)
  have h1 : ENNReal.ofReal r * ν (interior K) ≤ ∫⁻ y in interior K, G y ∂ν := by
    rw [← setLIntegral_const]
    refine setLIntegral_mono' hYm fun y hy => ?_
    have hy' : r < (G y).toReal := hKO (interior_subset hy)
    rw [← ENNReal.ofReal_toReal (hGf y)]
    exact ENNReal.ofReal_le_ofReal hy'.le
  have h2 := h1.trans (hD _ hYm)
  have hr0 : 0 ≤ r := (NNReal.coe_nonneg D).trans hr1.le
  have hnr : 0 < (ν (interior K)).toReal := ENNReal.toReal_pos hpos hfin
  have h3 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top hfin) h2
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hr0, ENNReal.coe_toReal] at h3
  exact absurd (le_of_mul_le_mul_right h3 hnr) (not_le.2 hr1)

end GlobalTheory.CompanionTheory.AvgFree.Lim

open GlobalTheory.CompanionTheory.AvgFree.Lim GlobalTheory.CompanionTheory.Hypotheses₂.OneV.AvgV in

theorem GlobalTheory.CompanionTheory.AvgFree.Lim.avg_tendsto_free : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (lv : Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdV v lv → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), HeckeCharacterZeroLocus.SiegelWeilU.IsHermND σ J → ∀ (n : ℕ) (mv : (HermR (Fv F v) σ n) → Measure (Fin n → Fin M → (Fv F v ⊗[F] E))), IsGramFibFree (Fv F v) σ J n (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n) mv → ∀ (c : (HermR (Fv F v) σ n)) (A : Set (Fin n → Fin M → (Fv F v ⊗[F] E))), IsCompact A → IsOpen A → ∀ Tt : ℕ → Set (Fin n → Fin M → (Fv F v ⊗[F] E)), Monotone Tt → (∀ j, IsCompact (Tt j) ∧ IsOpen (Tt j) ∧ Tt j ⊆ A ∧ Tt j ⊆ {X : (Fin n → Fin M → (Fv F v ⊗[F] E)) | LinearIndependent (Fv F v ⊗[F] E) X}) → A ∩ {X : (Fin n → Fin M → (Fv F v ⊗[F] E)) | LinearIndependent (Fv F v ⊗[F] E) X} ⊆ ⋃ j, Tt j → ∀ ε : ℕ → ℝ≥0, Filter.Tendsto ε Filter.atTop (nhds 0) → (∀ (j : ℕ) (Y : Set (HermR (Fv F v) σ n)), MeasurableSet Y → (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) ((A \ Tt j) ∩ gramIn (Fv F v) σ J Y) ≤ ε j * (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n) Y) → mv c A ≠ ⊤ ∧ ∀ U : ℕ → Set (HermR (Fv F v) σ n), (∀ k, IsCompact (U k) ∧ IsOpen (U k) ∧ (0 : (HermR (Fv F v) σ n)) ∈ U k) → Filter.Tendsto U Filter.atTop (nhds (0 : (HermR (Fv F v) σ n))).smallSets → (∀ k, MeasurableSet (A ∩ gramNear (Fv F v) σ J c (U k)) ∧ (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) (A ∩ gramNear (Fv F v) σ J c (U k)) ≠ ⊤) ∧ Filter.Tendsto (fun k => ((GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) (A ∩ gramNear (Fv F v) σ J c (U k))).toReal / ((GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n) (U k)).toReal) Filter.atTop (nhds (mv c A).toReal) := by
  intro F E _ _ _ _ _ σ hσ d b v lv hlv M J hJ n mv hmv c A hAc hAo Tt hTm hT hcov ε hε hden
  obtain ⟨r1, r2, r3, r4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI := r1
  haveI := r2
  haveI := r3
  haveI := r4
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨a1, a2, a3, a4, -, -, -, a8, a9, a10⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)
  haveI := a1
  haveI := a2
  haveI := a3
  haveI := a4
  haveI := a8 n M
  haveI := hlv.1
  obtain ⟨-, hW, hH⟩ := GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hσ (Fv F v) d b lv hlv.1
  haveI := hW n M
  haveI := hH n
  haveI : BorelSpace (HermR (Fv F v) σ n) := ⟨rfl⟩
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → Fv F v ⊗[F] E))
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → Fv F v ⊗[F] E))
  haveI : LocallyCompactSpace (HermR (Fv F v) σ n) := (a9 n).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (HermR (Fv F v) σ n) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n).IsNegInvariant :=
    Measure.IsAddHaarMeasure.isNegInvariant_of_regular _
  have I := GlobalTheory.T.local_fibre_measure_unramified_formula F E σ hσ d b v lv hlv M J hJ n mv hmv
  have hAm : MeasurableSet A := hAo.measurableSet

  obtain ⟨h0m, -, -, C, hC⟩ := I (Tt 0) (hT 0).1 (hT 0).2.1 (hT 0).2.2.2
  have hsplit : ∀ (j : ℕ) (Y : Set (HermR (Fv F v) σ n)), MeasurableSet Y →
      GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M (A ∩ gramIn (Fv F v) σ J Y) ≤
        GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M (Tt j ∩ gramIn (Fv F v) σ J Y) +
          ε j * GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n Y := by
    intro j Y hY
    refine (measure_mono ?_).trans ((measure_union_le (Tt j ∩ gramIn (Fv F v) σ J Y)
      ((A \ Tt j) ∩ gramIn (Fv F v) σ J Y)).trans (by gcongr; exact hden j Y hY))
    intro X hX
    by_cases h : X ∈ Tt j
    · exact Or.inl ⟨h, hX.2⟩
    · exact Or.inr ⟨⟨hX.1, h⟩, hX.2⟩
  have hbd : ∀ j, mv c (Tt j) ≤ ((C + ε 0 : ℝ≥0) : ℝ≥0∞) := by
    intro j
    obtain ⟨hjm, hjc, hjf, -⟩ := I (Tt j) (hT j).1 (hT j).2.1 (hT j).2.2.2
    refine le_of_forall_mean_le (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n) (fun y => mv y (Tt j)) hjc hjf _
      (fun Y hY => ?_) c
    rw [← hjm Y hY]
    refine (measure_mono (Set.inter_subset_inter_left _ (hT j).2.2.1)).trans ((hsplit 0 Y hY).trans ?_)
    rw [h0m Y hY, ENNReal.coe_add, add_mul]
    gcongr
    rw [← setLIntegral_const]
    exact setLIntegral_mono' hY fun y _ => hC y

  have hle : mv c A ≤ mv c (⋃ j, Tt j) := by
    have hcar := hmv.1 c
    refine (measure_mono (t := (⋃ j, Tt j) ∪ (gramR (Fv F v) σ J ⁻¹' {(c : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))} ∩
      {X : Fin n → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X})ᶜ) ?_).trans
      ((measure_union_le _ _).trans ?_)
    · intro X hX
      by_cases h : X ∈ (gramR (Fv F v) σ J ⁻¹' {(c : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))} ∩
        {X : Fin n → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X})
      · exact Or.inl (hcov ⟨hX, h.2⟩)
      · exact Or.inr h
    · have hcar' : mv c (gramR (Fv F v) σ J ⁻¹' {(c : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))} ∩
        {X : Fin n → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X})ᶜ = 0 := hcar
      rw [hcar', add_zero]
  have hsup : mv c (⋃ j, Tt j) = ⨆ j, mv c (Tt j) := hTm.measure_iUnion
  have heq : mv c A = ⨆ j, mv c (Tt j) :=
    le_antisymm (hle.trans hsup.le) (iSup_le fun j => measure_mono (hT j).2.2.1)
  have hfin : mv c A ≠ ⊤ := by
    rw [heq]
    exact ne_top_of_le_ne_top ENNReal.coe_ne_top (iSup_le hbd)
  have hlim : Filter.Tendsto (fun j => mv c (Tt j)) Filter.atTop (nhds (mv c A)) := by
    rw [heq]
    exact tendsto_atTop_iSup fun i j hij => measure_mono (hTm hij)
  refine ⟨hfin, fun U hU hUt => ?_⟩

  have hinv := GlobalTheory.CompanionTheory.SW.HermTop.sigma_sigma hσ
  let Q : (Fin n → Fin M → Fv F v ⊗[F] E) → HermR (Fv F v) σ n := fun X =>
    ⟨gramR (Fv F v) σ J X, GlobalTheory.CompanionTheory.SW.HermTop.gramR_mem (Fv F v) hinv hJ.1 X⟩
  have hQc : Continuous Q := (a10 n M J).subtype_mk _
  have hnear : ∀ W : Set (HermR (Fv F v) σ n), gramNear (Fv F v) σ J c W = (fun X => c - Q X) ⁻¹' W := by
    intro W
    ext X
    constructor
    · rintro ⟨u, hu, e⟩
      have : c - Q X = u := Subtype.ext e
      show c - Q X ∈ W
      rwa [this]
    · intro h
      exact ⟨c - Q X, h, rfl⟩
  let S : ℕ → Set (HermR (Fv F v) σ n) := fun k => (fun y => c - y) ⁻¹' U k
  have hgram : ∀ k, gramNear (Fv F v) σ J c (U k) = gramIn (Fv F v) σ J (S k) := by
    intro k
    rw [hnear]
    ext X
    constructor
    · intro h
      exact ⟨Q X, h, rfl⟩
    · rintro ⟨y, hy, e⟩
      have : y = Q X := Subtype.ext e.symm
      rw [this] at hy
      exact hy
  have hSo : ∀ k, IsOpen (S k) := fun k => (hU k).2.1.preimage (continuous_const.sub continuous_id)
  have hSm : ∀ k, MeasurableSet (S k) := fun k => (hSo k).measurableSet
  have hSc : ∀ k, c ∈ S k := fun k => by
    show c - c ∈ U k
    rw [sub_self]
    exact (hU k).2.2
  have hSU : ∀ k, GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n (S k) = GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n (U k) := fun k =>
    (Measure.measurePreserving_sub_left _ c).measure_preimage (hU k).2.1.measurableSet.nullMeasurableSet
  have hpos : ∀ k, GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n (S k) ≠ 0 := fun k =>
    (hSo k).measure_ne_zero _ ⟨c, hSc k⟩
  have htop : ∀ k, GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n (S k) ≠ ⊤ := fun k => by
    rw [hSU]
    exact (hU k).1.measure_lt_top.ne
  have hl : Filter.Tendsto S Filter.atTop (nhds c).smallSets := by
    rw [Filter.tendsto_smallSets_iff]
    intro t ht
    have hcont : Filter.Tendsto (fun u : HermR (Fv F v) σ n => c - u) (nhds 0) (nhds c) := by
      have : Continuous fun u : HermR (Fv F v) σ n => c - u := continuous_const.sub continuous_id
      simpa using this.tendsto 0
    have h0 := (Filter.tendsto_smallSets_iff.1 hUt) _ (hcont ht)
    filter_upwards [h0] with k hk s hs
    have := hk hs
    simpa using this
  have hAfin : ∀ B : Set (Fin n → Fin M → Fv F v ⊗[F] E), B ⊆ A → GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M B ≠ ⊤ :=
    fun B hB => ne_top_of_le_ne_top hAc.measure_lt_top.ne (measure_mono hB)
  refine ⟨fun k => ?_, ?_⟩
  · refine ⟨?_, hAfin _ Set.inter_subset_left⟩
    rw [hnear]
    exact (hAo.inter ((hU k).2.1.preimage (continuous_const.sub hQc))).measurableSet
  · refine tendsto_of_squeeze _
      (fun j k => (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M (Tt j ∩ gramIn (Fv F v) σ J (S k))).toReal /
        (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n (U k)).toReal)
      (fun j => (mv c (Tt j)).toReal) (fun j => (ε j : ℝ)) _ ?_ ((ENNReal.tendsto_toReal hfin).comp hlim) ?_ ?_ ?_
    · have h := NNReal.tendsto_coe.2 hε
      rwa [NNReal.coe_zero] at h
    · intro j
      obtain ⟨hjm, hjc, hjf, -⟩ := I (Tt j) (hT j).1 (hT j).2.1 (hT j).2.2.2
      have key := tendsto_mean (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n) (fun y => mv y (Tt j)) c hjc.continuousAt
        (Filter.Eventually.of_forall hjf) S hSm hl hpos htop
      refine key.congr fun k => ?_
      rw [hSU k, hjm (S k) (hSm k)]
    · intro j k
      rw [hgram k]
      refine div_le_div_of_nonneg_right (ENNReal.toReal_mono (hAfin _ Set.inter_subset_left) ?_) ENNReal.toReal_nonneg
      exact measure_mono (Set.inter_subset_inter_left _ (hT j).2.2.1)
    · intro j k
      rw [hgram k]
      have hp : 0 < (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n (U k)).toReal := by
        rw [← hSU k]
        exact ENNReal.toReal_pos (hpos k) (htop k)
      have hs := hsplit j (S k) (hSm k)
      rw [hSU k] at hs
      have hr := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hAfin _ (Set.inter_subset_inter_left _ (hT j).2.2.1 |>.trans Set.inter_subset_left),
        ENNReal.mul_ne_top ENNReal.coe_ne_top (by rw [← hSU k]; exact htop k)⟩) hs
      rw [ENNReal.toReal_add (hAfin _ (Set.inter_subset_inter_left _ (hT j).2.2.1 |>.trans Set.inter_subset_left))
        (ENNReal.mul_ne_top ENNReal.coe_ne_top (by rw [← hSU k]; exact htop k)), ENNReal.toReal_mul, ENNReal.coe_toReal] at hr
      rw [div_le_iff₀ hp, add_mul, div_mul_cancel₀ _ hp.ne']
      exact hr
