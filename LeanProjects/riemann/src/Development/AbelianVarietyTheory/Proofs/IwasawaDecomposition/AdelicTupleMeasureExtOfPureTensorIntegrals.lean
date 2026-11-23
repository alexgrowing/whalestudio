import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasurableEmbeddingAdelicTupleLocalComponentsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralPointsFinitePlaceTensorPropertiesStatement
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.GaugeEx.PureUniq

theorem finiteOnCompacts_of_integrable {Z : Type} [TopologicalSpace Z] [T2Space Z]
    [LocallyCompactSpace Z] [MeasurableSpace Z] (m : Measure Z)
    (h : ∀ g : Z → ℝ, Continuous g → HasCompactSupport g → Integrable g m) :
    IsFiniteMeasureOnCompacts m := by
  refine ⟨fun C hC => ?_⟩
  obtain ⟨f, h1, -, hs, -⟩ := exists_continuous_one_zero_of_isCompact hC isClosed_empty
    (Set.disjoint_empty C)
  have := (h f f.continuous hs).measure_norm_ge_lt_top (ε := 1) one_pos
  refine lt_of_le_of_lt (measure_mono fun x hx => ?_) this
  simp [h1 hx]

theorem basis_compact_open (Z : Type) [TopologicalSpace Z] [T2Space Z] [LocallyCompactSpace Z]
    [TotallyDisconnectedSpace Z] :
    TopologicalSpace.IsTopologicalBasis {U : Set Z | IsCompact U ∧ IsOpen U} := by
  refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds (fun u hu => hu.2) ?_
  intro a u hau hu
  obtain ⟨C, hCa, hCu, hC⟩ := local_compact_nhds (hu.mem_nhds hau)
  obtain ⟨V, hV, haV, hVC⟩ := (loc_compact_Haus_tot_disc_of_zero_dim (H := Z)).mem_nhds_iff.mp hCa
  exact ⟨V, ⟨hC.of_isClosed_subset hV.1 hVC, hV.2⟩, haV, hVC.trans hCu⟩

theorem exists_seq_cover {Z : Type} [TopologicalSpace Z] [T2Space Z] [LocallyCompactSpace Z]
    [TotallyDisconnectedSpace Z] [SecondCountableTopology Z] (L : Set Z)
    (hL : IsCompact L ∧ IsOpen L) :
    ∃ W : ℕ → Set Z, W 0 = L ∧ (∀ k, IsCompact (W k) ∧ IsOpen (W k)) ∧ ∀ z, ∃ k, z ∈ W k := by
  have h : ∀ z : Z, ∃ V : Set Z, (IsCompact V ∧ IsOpen V) ∧ z ∈ V := fun z => by
    obtain ⟨V, hV, hz, -⟩ := (basis_compact_open Z).mem_nhds_iff.mp (Filter.univ_mem (f := 𝓝 z))
    exact ⟨V, hV, hz⟩
  choose f hf hzf using h
  obtain ⟨s, hs, hcov⟩ := TopologicalSpace.countable_cover_nhds (f := f)
    fun z => (hf z).2.mem_nhds (hzf z)
  have hc : (insert L (f '' s)).Countable := (hs.image f).insert L
  obtain ⟨g, hg⟩ := hc.exists_eq_range (Set.insert_nonempty _ _)
  have hg' : ∀ k, IsCompact (g k) ∧ IsOpen (g k) := fun k => by
    have : g k ∈ insert L (f '' s) := hg ▸ Set.mem_range_self k
    rcases this with h | ⟨z, -, h⟩
    · rw [h]; exact hL
    · rw [← h]; exact hf z
  refine ⟨fun k => Nat.casesOn k L g, rfl, fun k => ?_, fun z => ?_⟩
  · cases k with
    | zero => exact hL
    | succ k => exact hg' k
  · have : z ∈ ⋃ x ∈ s, f x := hcov ▸ Set.mem_univ z
    obtain ⟨x, hx, hzx⟩ := Set.mem_iUnion₂.mp this
    have : f x ∈ Set.range g := hg ▸ Set.mem_insert_of_mem _ ⟨x, hx, rfl⟩
    obtain ⟨k, hk⟩ := this
    exact ⟨k + 1, by simpa [hk] using hzx⟩

theorem ext_of_pure {X I Z₀ : Type} {Z : I → Type} [mX : MeasurableSpace X] [Countable I]
    [TopologicalSpace Z₀] [T2Space Z₀] [LocallyCompactSpace Z₀] [SecondCountableTopology Z₀]
    [MeasurableSpace Z₀] [BorelSpace Z₀]
    [∀ v, TopologicalSpace (Z v)] [∀ v, T2Space (Z v)] [∀ v, LocallyCompactSpace (Z v)]
    [∀ v, TotallyDisconnectedSpace (Z v)] [∀ v, SecondCountableTopology (Z v)]
    [∀ v, MeasurableSpace (Z v)] [∀ v, BorelSpace (Z v)]
    (p : X → Z₀) (q : ∀ v, X → Z v) (L : ∀ v, Set (Z v)) (hL : ∀ v, IsCompact (L v) ∧ IsOpen (L v))
    (he : MeasurableEmbedding fun x => (p x, fun v => q v x))
    (hr : ∀ x, ∀ᶠ v in Filter.cofinite, q v x ∈ L v) (ν ν' : Measure X)
    (h : ∀ K : ∀ v, Set (Z v), (∀ v, IsCompact (K v) ∧ IsOpen (K v)) →
      (∀ᶠ v in Filter.cofinite, K v = L v) → ∀ g : Z₀ → ℝ, Continuous g → HasCompactSupport g →
      IntegrableOn (fun x => g (p x)) {x | ∀ v, q v x ∈ K v} ν ∧
      IntegrableOn (fun x => g (p x)) {x | ∀ v, q v x ∈ K v} ν' ∧
      ∫ x in {x | ∀ v, q v x ∈ K v}, g (p x) ∂ν = ∫ x in {x | ∀ v, q v x ∈ K v}, g (p x) ∂ν') :
    ν = ν' := by
  classical
  have hp : Measurable p := measurable_fst.comp he.measurable
  have hq : ∀ v, Measurable (q v) := fun v =>
    (measurable_pi_apply v).comp (measurable_snd.comp he.measurable)
  have hS : ∀ K : ∀ v, Set (Z v), (∀ v, IsCompact (K v) ∧ IsOpen (K v)) →
      MeasurableSet {x | ∀ v, q v x ∈ K v} := fun K hK => by
    rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun v => hq v (hK v).2.measurableSet
  have key : ∀ K : ∀ v, Set (Z v), (∀ v, IsCompact (K v) ∧ IsOpen (K v)) →
      (∀ᶠ v in Filter.cofinite, K v = L v) → ∀ A : Set Z₀, MeasurableSet A →
      ν (p ⁻¹' A ∩ {x | ∀ v, q v x ∈ K v}) = ν' (p ⁻¹' A ∩ {x | ∀ v, q v x ∈ K v}) ∧
      (IsCompact A → ν (p ⁻¹' A ∩ {x | ∀ v, q v x ∈ K v}) < ∞) := by
    intro K hK hKL A hA
    have f1 : IsFiniteMeasureOnCompacts ((ν.restrict {x | ∀ v, q v x ∈ K v}).map p) :=
      finiteOnCompacts_of_integrable _ fun g hg hs =>
        (integrable_map_measure hg.aestronglyMeasurable hp.aemeasurable).2 (h K hK hKL g hg hs).1
    have f2 : IsFiniteMeasureOnCompacts ((ν'.restrict {x | ∀ v, q v x ∈ K v}).map p) :=
      finiteOnCompacts_of_integrable _ fun g hg hs =>
        (integrable_map_measure hg.aestronglyMeasurable hp.aemeasurable).2 (h K hK hKL g hg hs).2.1
    have e : (ν.restrict {x | ∀ v, q v x ∈ K v}).map p =
        (ν'.restrict {x | ∀ v, q v x ∈ K v}).map p := by
      refine Measure.ext_of_integral_eq_on_compactlySupported fun f => ?_
      have hf : Continuous (f : Z₀ → ℝ) := f.continuous
      rw [integral_map hp.aemeasurable hf.aestronglyMeasurable,
        integral_map hp.aemeasurable hf.aestronglyMeasurable]
      exact (h K hK hKL f hf f.hasCompactSupport).2.2
    have e1 : ∀ m : Measure X, ((m.restrict {x | ∀ v, q v x ∈ K v}).map p) A =
        m (p ⁻¹' A ∩ {x | ∀ v, q v x ∈ K v}) := fun m => by
      rw [Measure.map_apply hp hA, Measure.restrict_apply (hp hA)]
    refine ⟨by rw [← e1, ← e1, e], fun hc => ?_⟩
    rw [← e1]
    exact hc.measure_lt_top
  choose W hW0 hW hWc using fun v => exists_seq_cover (L v) (hL v)
  set G : Set (Set X) := {t | (∃ A, MeasurableSet A ∧ t = p ⁻¹' A) ∨
    ∃ v U, (IsCompact U ∧ IsOpen U) ∧ t = q v ⁻¹' U} with hG
  have hGm : ∀ t ∈ G, MeasurableSet t := by
    rintro t (⟨A, hA, rfl⟩ | ⟨v, U, hU, rfl⟩)
    · exact hp hA
    · exact hq v hU.2.measurableSet
  have hgen : mX = MeasurableSpace.generateFrom (generatePiSystem G) := by
    rw [generateFrom_generatePiSystem_eq]
    refine le_antisymm ?_ (MeasurableSpace.generateFrom_le hGm)
    have hm : @Measurable X _ (MeasurableSpace.generateFrom G) _
        fun x => (p x, fun v => q v x) := by
      refine Measurable.prodMk (m := MeasurableSpace.generateFrom G) ?_ ?_
      · exact fun A hA => MeasurableSpace.measurableSet_generateFrom (Or.inl ⟨A, hA, rfl⟩)
      · refine @measurable_pi_lambda _ _ _ (MeasurableSpace.generateFrom G) _ _ fun v => ?_
        have hb := (BorelSpace.measurable_eq (α := Z v)).trans
          (basis_compact_open (Z v)).borel_eq_generateFrom
        have : @Measurable X (Z v) (MeasurableSpace.generateFrom G)
            (MeasurableSpace.generateFrom {U : Set (Z v) | IsCompact U ∧ IsOpen U}) (q v) :=
          @measurable_generateFrom _ _ (MeasurableSpace.generateFrom G) _ _ fun U hU =>
            MeasurableSpace.measurableSet_generateFrom (Or.inr ⟨v, U, hU, rfl⟩)
        rw [← hb] at this
        exact this
    have := hm.comap_le
    rwa [he.comap_eq] at this
  have hpi : ∀ t, generatePiSystem G t → ∀ K : ∀ v, Set (Z v),
      (∀ v, IsCompact (K v) ∧ IsOpen (K v)) → (∀ᶠ v in Filter.cofinite, K v = L v) →
      ∀ A : Set Z₀, MeasurableSet A → ∃ K' : ∀ v, Set (Z v),
      (∀ v, IsCompact (K' v) ∧ IsOpen (K' v)) ∧ (∀ᶠ v in Filter.cofinite, K' v = L v) ∧
      ∃ A' : Set Z₀, MeasurableSet A' ∧ t ∩ (p ⁻¹' A ∩ {x | ∀ v, q v x ∈ K v}) =
        p ⁻¹' A' ∩ {x | ∀ v, q v x ∈ K' v} := by
    intro t ht
    induction ht with
    | base hs =>
      intro K hK hKL A hA
      rcases hs with ⟨B, hB, rfl⟩ | ⟨w, U, hU, rfl⟩
      · exact ⟨K, hK, hKL, B ∩ A, hB.inter hA, by rw [Set.preimage_inter, Set.inter_assoc]⟩
      · refine ⟨Function.update K w (U ∩ K w), fun v => ?_, ?_, A, hA, ?_⟩
        · by_cases hv : v = w
          · subst hv
            rw [Function.update_self]
            exact ⟨hU.1.inter (hK v).1, hU.2.inter (hK v).2⟩
          · rw [Function.update_of_ne hv]; exact hK v
        · filter_upwards [hKL, Filter.eventually_cofinite_ne w] with v h1 h2
          rw [Function.update_of_ne h2, h1]
        · ext x
          simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq]
          constructor
          · rintro ⟨h1, h2, h3⟩
            refine ⟨h2, fun v => ?_⟩
            by_cases hv : v = w
            · subst hv
              rw [Function.update_self]
              exact ⟨h1, h3 v⟩
            · rw [Function.update_of_ne hv]; exact h3 v
          · rintro ⟨h2, h3⟩
            have h4 := h3 w
            rw [Function.update_self] at h4
            refine ⟨h4.1, h2, fun v => ?_⟩
            by_cases hv : v = w
            · subst hv; exact h4.2
            · have := h3 v
              rwa [Function.update_of_ne hv] at this
    | inter _ _ _ ih1 ih2 =>
      intro K hK hKL A hA
      obtain ⟨K1, hK1, hKL1, A1, hA1, e1⟩ := ih2 K hK hKL A hA
      obtain ⟨K2, hK2, hKL2, A2, hA2, e2⟩ := ih1 K1 hK1 hKL1 A1 hA1
      exact ⟨K2, hK2, hKL2, A2, hA2, by rw [Set.inter_assoc, e1, e2]⟩
  refine (Measure.ext_iff_of_iUnion_eq_univ (s := fun j : (I →₀ ℕ) × ℕ =>
    p ⁻¹' (compactCovering Z₀ j.2) ∩ {x | ∀ v, q v x ∈ W v (j.1 v)}) ?_).2 ?_
  · refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ?_
    obtain ⟨k, hk⟩ := exists_mem_compactCovering (p x)
    choose c hc using fun v => hWc v (q v x)
    have hfin : (Function.support fun v => if q v x ∈ L v then 0 else c v).Finite := by
      refine (Filter.eventually_cofinite.1 (hr x)).subset fun v hv hv' => hv ?_
      simp [hv']
    refine ⟨(Finsupp.ofSupportFinite _ hfin, k), hk, fun v => ?_⟩
    show q v x ∈ W v (if q v x ∈ L v then 0 else c v)
    split_ifs with hv
    · rw [hW0]; exact hv
    · exact hc v
  · rintro ⟨j, k⟩
    have hC := isCompact_compactCovering Z₀ k
    have hj : ∀ᶠ v in Filter.cofinite, W v (j v) = L v := by
      filter_upwards [j.support.eventually_cofinite_notMem] with v hv
      rw [Finsupp.notMem_support_iff.1 hv, hW0]
    have k0 := key (fun v => W v (j v)) (fun v => hW v _) hj _ hC.measurableSet
    have : IsFiniteMeasure (ν.restrict
        (p ⁻¹' (compactCovering Z₀ k) ∩ {x | ∀ v, q v x ∈ W v (j v)})) :=
      isFiniteMeasure_restrict.2 (k0.2 hC).ne
    refine ext_of_generate_finite _ hgen (isPiSystem_generatePiSystem G) (fun t ht => ?_) ?_
    · have htm : MeasurableSet t := generatePiSystem_measurableSet hGm t ht
      obtain ⟨K', hK', hKL', A', hA', e⟩ :=
        hpi t ht (fun v => W v (j v)) (fun v => hW v _) hj _ hC.measurableSet
      simp only
      rw [Measure.restrict_apply htm, Measure.restrict_apply htm, e]
      exact (key K' hK' hKL' A' hA').1
    · simp only [Measure.restrict_apply_univ]
      exact k0.1

theorem isSB_indicator {V : Type} [TopologicalSpace V] [T2Space V] {K : Set V}
    (hK : IsCompact K ∧ IsOpen K) : IsSB (K.indicator (1 : V → ℂ)) := by
  refine ⟨?_, HasCompactSupport.intro hK.1 fun x hx => Set.indicator_of_notMem hx _⟩
  classical
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : x ∈ K
  · filter_upwards [hK.2.mem_nhds hx] with y hy
    simp [hx, hy]
  · filter_upwards [hK.1.isClosed.isOpen_compl.mem_nhds hx] with y hy
    have hy' : y ∉ K := hy
    simp [hx, hy']

theorem measure_ext_of_pure (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (d' : ℕ) (b' : Module.Basis (Fin d') F E) (n M : ℕ)
    (ν ν' : Measure (Fin n → Fin M → AF F ⊗[F] E))
    (h : ∀ (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (Φinf : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ)
      (Φf : (Fin n → Fin M → Af F ⊗[F] E) → ℂ)
      (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ),
      Continuous Φinf → HasCompactSupport Φinf → IsPureFin b' Φf Φv → IsProdInfFin Φ Φinf Φf →
      Integrable Φ ν ∧ Integrable Φ ν' ∧ ∫ X, Φ X ∂ν = ∫ X, Φ X ∂ν') : ν = ν' := by
  classical
  have : FiniteDimensional F E := Module.Finite.of_basis b'
  have : Countable (HeightOneSpectrum (𝓞 F)) := GlobalTheory.AdelicUnitaryTop.countable_heightOneSpectrum F
  have : ∀ v : HeightOneSpectrum (𝓞 F), TotallyDisconnectedSpace (Fv F v ⊗[F] E) := fun v => by
    obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (Fv F v)
    exact e.symm.totallyDisconnectedSpace
  obtain ⟨he, hrange, -, -⟩ := GlobalTheory.T.measurableEmbedding_adelicTuple_localComponents F E d' b' n M
  have hint := (GlobalTheory.T.integralPointsFinitePlaceTensor_properties F E (AlgHom.id F E) d' b').1
  have hL : ∀ v : HeightOneSpectrum (𝓞 F), IsCompact (latV (n := n) (M := M) b' v) ∧
      IsOpen (latV (n := n) (M := M) b' v) := fun v => by
    have e : latV (n := n) (M := M) b' v =
        Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => intV b' v := by
      ext Y
      simp [mem_latV_iff]
    rw [e]
    exact ⟨isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => (hint v).1,
      isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => (hint v).2⟩
  have hr : ∀ X : Fin n → Fin M → AF F ⊗[F] E, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      projV v (projFin X) ∈ latV b' v := fun X => by
    have := Set.mem_range_self (f := fun X : (Fin n → Fin M → AF F ⊗[F] E) =>
      (projInf X, fun v : HeightOneSpectrum (𝓞 F) => projV v (projFin X))) X
    rw [hrange] at this
    exact this
  refine ext_of_pure projInf (fun v X => projV v (projFin X)) (fun v => latV b' v) hL he hr ν ν' ?_
  intro K hK hKL g hg hs
  have hS : MeasurableSet {X : Fin n → Fin M → AF F ⊗[F] E | ∀ v, projV v (projFin X) ∈ K v} := by
    rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun v =>
      ((measurable_pi_apply v).comp (measurable_snd.comp he.measurable)) (hK v).2.measurableSet
  have hprod : IsProdInfFin
      (Set.indicator {X : Fin n → Fin M → AF F ⊗[F] E | ∀ v, projV v (projFin X) ∈ K v}
        fun X => ((g (projInf X) : ℝ) : ℂ))
      (fun Y => ((g Y : ℝ) : ℂ)) (fun X => ∏ᶠ v, (K v).indicator (1 : (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ) (projV v X)) := by
    intro X
    by_cases hX : ∀ v, projV v (projFin X) ∈ K v
    · rw [Set.indicator_of_mem (by exact hX)]
      simp [hX]
    · rw [Set.indicator_of_notMem (by exact hX)]
      obtain ⟨w, hw⟩ := not_forall.1 hX
      have hfin : (Function.mulSupport fun v =>
          (K v).indicator (1 : (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ) (projV v (projFin X))).Finite := by
        refine (Filter.eventually_cofinite.1 ((hr X).and hKL)).subset fun v hv hv' => hv ?_
        have : projV v (projFin X) ∈ K v := hv'.2 ▸ hv'.1
        simp [this]
      show 0 = _ * ∏ᶠ v, (K v).indicator (1 : (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ) (projV v (projFin X))
      rw [finprod_eq_zero _ w (Set.indicator_of_notMem hw _) hfin, mul_zero]
  obtain ⟨h1, h2, h3⟩ := h _ _ _ (fun v => (K v).indicator 1) (Complex.continuous_ofReal.comp hg)
    (hs.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero)
    ⟨fun v => isSB_indicator (hK v), hKL.mono fun v hv => by simp only [hv], fun _ => rfl⟩ hprod
  rw [integrable_indicator_iff hS] at h1 h2
  rw [integral_indicator hS, integral_indicator hS, integral_complex_ofReal,
    integral_complex_ofReal] at h3
  exact ⟨h1.re, h2.re, by exact_mod_cast h3⟩

end GlobalTheory.GaugeEx.PureUniq
