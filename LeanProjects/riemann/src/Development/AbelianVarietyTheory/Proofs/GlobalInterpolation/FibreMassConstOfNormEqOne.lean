import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SelfDualUnramifiedPlaces
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory

theorem addHaar_map_eq_of_preimage_eq {G : Type} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsAddHaarMeasure] (T : G ≃+ G)
    (hT : Continuous T) (hT' : Continuous T.symm) {S : Set G} (hS : MeasurableSet S)
    (hpos : μ S ≠ 0) (hfin : μ S ≠ ⊤) (hpre : T ⁻¹' S = S) : Measure.map T μ = μ := by
  haveI : (Measure.map T μ).IsAddHaarMeasure := AddEquiv.isAddHaarMeasure_map μ T hT hT'
  have hk := Measure.isAddLeftInvariant_eq_smul (Measure.map T μ) μ
  set k := Measure.addHaarScalarFactor (Measure.map T μ) μ
  have hm : Measure.map T μ S = μ S := by
    rw [Measure.map_apply hT.measurable hS, hpre]
  have hk1 : k = 1 := by
    rw [hk, Measure.smul_apply] at hm
    have h1 : (k : ENNReal) * μ S = 1 * μ S := by
      rw [one_mul]
      simpa [ENNReal.smul_def] using hm
    have := (ENNReal.mul_left_inj hpos hfin).1 h1
    exact_mod_cast this
  rw [hk, hk1, one_smul]

theorem fibre_mass_const_of_norm_eq_one {K : Type} [NormedField K] [ProperSpace K]
    [MeasurableSpace K] [BorelSpace K] (hU : IsOpen {u : K | ‖u‖ = 1})
    {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [μ.IsAddHaarMeasure] (ν : Measure K) [ν.IsAddHaarMeasure] (q : V → K)
    (hq : Continuous q) (fib : K → Measure V)
    (hfib : IsFibreFamily μ q id Set.univ ν {c | c ≠ 0} fib) (L : AddSubgroup V)
    (hLc : IsCompact (L : Set V)) (hLo : IsOpen (L : Set V))
    (hact : ∀ u : K, ‖u‖ = 1 → ∃ T : V ≃+ V, Continuous T ∧ Continuous T.symm ∧
      (∀ x, T x ∈ L ↔ x ∈ L) ∧ ∀ x, q (T x) = u * q x) (β : K) (hβ : ‖β‖ = 1) :
    fib β (L : Set V) ≠ ⊤ ∧
      (fib β).real (L : Set V) * ν.real {u | ‖u‖ = 1} = μ.real {x | x ∈ L ∧ ‖q x‖ = 1} := by
  obtain ⟨h1, h2, h3⟩ := hfib
  have hLcl : IsClopen (L : Set V) := ⟨L.isClosed_of_isOpen hLo, hLo⟩
  have hLm : MeasurableSet (L : Set V) := hLo.measurableSet
  have hφc : Continuous ((L : Set V).indicator (fun _ => (1 : ℝ))) :=
    hLcl.continuous_indicator continuous_const
  have hφs : HasCompactSupport ((L : Set V).indicator (fun _ => (1 : ℝ))) :=
    HasCompactSupport.intro hLc (fun x hx => Set.indicator_of_notMem hx _)
  obtain ⟨hI, hC⟩ := h3 _ hφc hφs (Set.subset_univ _)
  have hG : ∀ b, ∫ v, (L : Set V).indicator (fun _ => (1 : ℝ)) v ∂(fib b)
      = (fib b L).toReal := by
    intro b
    rw [integral_indicator hLm, setIntegral_const, smul_eq_mul, mul_one]
    rfl
  simp only [hG] at hC
  have hfin : ∀ b : K, b ≠ 0 → fib b L ≠ ⊤ := by
    intro b hb
    have := (integrable_indicator_iff hLm).mp (hI b hb)
    rcases (integrableOn_const_iff (by simp)).mp this with h | h
    · simp at h
    · exact h.ne
  have hne : ∀ b : K, ‖b‖ = 1 → b ≠ 0 := by
    rintro b hb rfl
    simp at hb
  have hμ : ∀ S : Set K, MeasurableSet S → μ (L ∩ q ⁻¹' S) = ∫⁻ b in S, fib b L ∂ν := by
    intro S hSm
    have hpm : MeasurableSet (q ⁻¹' S) := hq.measurable hSm
    have hfb : ∀ b, fib b (L ∩ q ⁻¹' S) = S.indicator (fun b => fib b L) b := by
      intro b
      have hae : ∀ᵐ v ∂(fib b), q v = b := by
        have := h1 b
        rw [Set.inter_univ] at this
        exact this
      by_cases hb : b ∈ S
      · rw [Set.indicator_of_mem hb]
        refine measure_congr ?_
        filter_upwards [hae] with v hv
        apply propext
        constructor
        · exact fun h => h.1
        · exact fun h => ⟨h, show q v ∈ S from hv ▸ hb⟩
      · rw [Set.indicator_of_notMem hb]
        refine measure_mono_null ?_ hae
        intro v hv hv'
        have e : q v = b := hv'
        exact hb (e ▸ hv.2)
    have := h2 (((L : Set V) ∩ q ⁻¹' S).indicator 1) (measurable_one.indicator (hLm.inter hpm))
    simp only [Measure.restrict_univ, lintegral_indicator_one (hLm.inter hpm), hfb] at this
    rw [this, lintegral_indicator hSm]
  set U : Set K := {u : K | ‖u‖ = 1} with hUdef
  have hUm : MeasurableSet U := hU.measurableSet
  have hUc : IsCompact U := by
    have : U = Metric.sphere (0 : K) 1 := by ext; simp [hUdef]
    rw [this]; exact isCompact_sphere _ _
  have hCU : ContinuousOn (fun b => (fib b L).toReal) U := hC.mono (fun b hb => hne b hb)
  have hR : ∀ S : Set K, MeasurableSet S → S ⊆ U →
      ∫ b in S, (fib b L).toReal ∂ν = (μ (L ∩ q ⁻¹' S)).toReal := by
    intro S hSm hSU
    rw [hμ S hSm, integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => ENNReal.toReal_nonneg)
      ((hCU.integrableOn_compact hUc).mono_set hSU).aestronglyMeasurable]
    congr 1
    exact setLIntegral_congr_fun hSm (fun b hb => ENNReal.ofReal_toReal (hfin b (hne b (hSU hb))))
  have hconst : ∀ t : K, ‖t‖ = 1 → (fib t L).toReal = (fib β L).toReal := by
    intro t ht
    have hu : ‖t / β‖ = 1 := by rw [norm_div, ht, hβ, div_one]
    set u := t / β with hudef
    have hu0 : u ≠ 0 := hne u hu
    obtain ⟨T, hT, hT', hTL, hTq⟩ := hact u hu
    have hTμ : Measure.map T μ = μ :=
      addHaar_map_eq_of_preimage_eq μ T hT hT' hLm
        (hLo.measure_pos μ ⟨0, L.zero_mem⟩).ne' hLc.measure_lt_top.ne (Set.ext hTL)
    let M : K ≃+ K := AddAut.mulLeft (Units.mk0 u hu0)
    have hM : ∀ x, M x = u * x := fun x => rfl
    have hMc : Continuous M := continuous_const.mul continuous_id
    have hMc' : Continuous M.symm := continuous_const.mul continuous_id
    have hMU : M ⁻¹' U = U := by
      ext x
      simp [hUdef, hM, hu]
    have hMν : Measure.map M ν = ν :=
      addHaar_map_eq_of_preimage_eq ν M hMc hMc' hUm
        (hU.measure_pos ν ⟨1, by simp [hUdef]⟩).ne' hUc.measure_lt_top.ne hMU
    let H : K ≃ₜ K := { M.toEquiv with continuous_toFun := hMc, continuous_invFun := hMc' }
    have hMe : MeasurableEmbedding M := H.measurableEmbedding
    have hCM : ContinuousOn (fun b => (fib (M b) L).toReal) U :=
      hCU.comp hMc.continuousOn (fun x hx => by rw [← hMU] at hx; exact hx)
    have hint : ∀ S : Set K, MeasurableSet S → S ⊆ U →
        ∫ b in S, (fib (M b) L).toReal ∂ν = ∫ b in S, (fib b L).toReal ∂ν := by
      intro S hSm hSU
      have hS' : MeasurableSet (M '' S) := hMe.measurableSet_image.2 hSm
      have hSU' : M '' S ⊆ U := by
        rintro _ ⟨x, hx, rfl⟩
        have := hSU hx
        rw [← hMU] at this
        exact this
      have e1 := hMe.setIntegral_map (μ := ν) (fun b => (fib b L).toReal) (M '' S)
      rw [hMν, Set.preimage_image_eq _ M.injective] at e1
      rw [← e1, hR _ hS' hSU', hR _ hSm hSU]
      congr 1
      conv_lhs => rw [← hTμ]
      rw [Measure.map_apply hT.measurable (hLm.inter (hq.measurable hS'))]
      congr 1
      ext x
      simp only [Set.mem_preimage, Set.mem_inter_iff, SetLike.mem_coe, hTL, hTq, ← hM,
        M.injective.mem_set_image]
    have hae : (fun b => (fib (M b) L).toReal) =ᵐ[ν.restrict U] fun b => (fib b L).toReal := by
      refine Integrable.ae_eq_of_forall_setIntegral_eq _ _ (hCM.integrableOn_compact hUc)
        (hCU.integrableOn_compact hUc) (fun S hSm _ => ?_)
      rw [Measure.restrict_restrict hSm]
      exact hint _ (hSm.inter hUm) Set.inter_subset_right
    have := Measure.eqOn_open_of_ae_eq hae hU hCM hCU (show β ∈ U from hβ)
    simp only [hM] at this
    rwa [hudef, div_mul_cancel₀ _ (hne β hβ)] at this
  refine ⟨hfin β (hne β hβ), ?_⟩
  have := hR U hUm subset_rfl
  rw [setIntegral_congr_fun hUm (g := fun _ => (fib β L).toReal) (fun t ht => hconst t ht),
    setIntegral_const, smul_eq_mul, mul_comm] at this
  exact this

theorem fibre_mass_mul_units_eq : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (ν : Measure (Fv F v)) [ν.IsAddHaarMeasure] (q : V → Fv F v), Continuous q → ∀ (fib : Fv F v → Measure V), IsFibreFamily μ q id Set.univ ν {c | c ≠ 0} fib → ∀ (L : AddSubgroup V), IsCompact (L : Set V) → IsOpen (L : Set V) → (∀ u : Fv F v, Valued.v u = 1 → ∃ T : V ≃+ V, Continuous T ∧ Continuous T.symm ∧ (∀ x, T x ∈ L ↔ x ∈ L) ∧ ∀ x, q (T x) = u * q x) → ∀ β : Fv F v, Valued.v β = 1 → fib β (L : Set V) ≠ ⊤ ∧ (fib β).real (L : Set V) * ν.real {u | Valued.v u = 1} = μ.real {x | x ∈ L ∧ Valued.v (q x) = 1} := by
  intro F _ _ v V _ _ _ _ _ _ _ μ _ ν _ q hq fib hfib L hLc hLo hact β hβ
  haveI := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  have hn : ∀ u : Fv F v, Valued.v u = 1 ↔ ‖u‖ = 1 := by
    intro u
    rw [le_antisymm_iff, le_antisymm_iff, Valued.toNormedField.norm_le_one_iff,
      Valued.toNormedField.one_le_norm_iff]
  have hU : IsOpen {u : Fv F v | ‖u‖ = 1} := by
    have := IsUltrametricDist.isOpen_sphere (0 : Fv F v) (r := 1) one_ne_zero
    convert this using 1
    ext
    simp
  simp only [hn] at hact hβ ⊢
  exact fibre_mass_const_of_norm_eq_one hU μ ν q hq fib hfib L hLc hLo hact β hβ

end GlobalTheory
