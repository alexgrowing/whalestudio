import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.HarishChandraDescent.Commutant
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.HarishChandraMultiplicityBound
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Arbitrary
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.ExistsKhwGenSubOfKType

noncomputable section

open Finset
open scoped InnerProductSpace

namespace PositivityTheory.RgHe3

open ReciprocityTheory.ChartRestriction.DS

namespace DiscreteSeriesData

theorem card_le {n : ℕ} (p : Fin n → Prop) [DecidablePred p] : ((univ.filter p).card : ℝ) ≤ n := by
  have h := Finset.card_filter_le (Finset.univ : Finset (Fin n)) p
  rw [Finset.card_univ, Fintype.card_fin] at h
  exact_mod_cast h

theorem npq_le {n : ℕ} (ε : Fin n → Bool) : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) ≤ (n : ℝ) ^ 3 := by
  have h1 : (pOf ε : ℝ) ≤ n := card_le _
  have h2 : (qOf ε : ℝ) ≤ n := card_le _
  have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h3 : (0 : ℝ) ≤ pOf ε := Nat.cast_nonneg _
  have h4 : (0 : ℝ) ≤ qOf ε := Nat.cast_nonneg _
  calc (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) ≤ n * n * n := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left h1 h0) h2 h4 (by positivity)
    _ = (n : ℝ) ^ 3 := by ring

end DiscreteSeriesData

open DiscreteSeriesData in
theorem discrete_series_data_holds : DSData := by
  intro n ε H i1 i2 i3 π hU lam h hHC hgap hh hDS
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hlt : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h := by
    linarith [npq_le ε]
  obtain ⟨hCas, -, -, hSm, -⟩ :=
    ReciprocityTheory.ChartRestriction.DS.isDS_props_of_gap n ε lam hHC h hgap hlt H π hDS
  have hD := isDerivedOn_smE (ε := ε) (σ := π) hU
  have hmemD : ∀ v : H, v ∈ smD ε π ↔ IsSmoothVecU ε π v := fun v =>
    (exists_smoothDerived ε π).choose_spec.choose_spec.1 v
  have part1 : ∀ x : smD ε π, casimir (smE ε π) x = ((casVal lam : ℝ) : ℂ) • x := by
    intro x
    apply Subtype.ext
    rw [← casU_eq_casimir hD x, Submodule.coe_smul]
    exact hCas x ((hmemD x).1 x.2)
  obtain ⟨S, hS⟩ := hDS.2.2.2.2.2.1
  have hSle : S ≤ smD ε π := fun v hv => (hmemD v).2 (hSm S hS.1 hS.2.1 v hv)
  obtain ⟨w, hwS, hw0, hw⟩ := exists_isKHWVec_of_isKTypeOf hU hD hS hSle
  refine ⟨part1, ?_, ?_⟩
  · refine ⟨((‖w‖ : ℂ))⁻¹ • w, norm_smul_inv_norm hw0, ?_, ?_⟩
    · intro a
      rw [LinearMap.map_smul, hw.1 a, smul_comm]
      rfl
    · intro a b hab he
      rw [LinearMap.map_smul, hw.2 a b hab he, smul_zero]
  · let V : Submodule ℂ (smD ε π) := S.comap (smD ε π).subtype
    haveI : FiniteDimensional ℂ S := hS.1
    have hmapV : V.map (smD ε π).subtype = S := by
      rw [Submodule.map_comap_subtype]
      exact inf_eq_right.mpr hSle
    have hVfd : FiniteDimensional ℂ V := by
      haveI hV : FiniteDimensional ℂ (V.map (smD ε π).subtype) := by
        rw [hmapV]
        infer_instance
      exact (Submodule.equivMapOfInjective _ (Submodule.injective_subtype _) V).symm.finiteDimensional
    have hVk : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ u ∈ V, (u : H) = π k v := by
      intro k hk v hv
      refine ⟨⟨π k v, hD.kStable k hk v v.2⟩, ?_, rfl⟩
      exact hS.2.1 k hk v hv
    have hVks : IsKStableSub ε (smE ε π) V := isKStableSub_of_kStable hU hD V hVfd hVk
    have hwV : w ∈ V := hwS
    have hirr : IsKIrrHW ε (smE ε π) (lowK ε lam) V := by
      refine ⟨hVfd, hVks, ?_, w, hwV, hw0, hw⟩
      intro S' hS'le hS'ks
      have hS'fd : FiniteDimensional ℂ S' := Submodule.finiteDimensional_of_le hS'le
      have hS'k := kStable_of_isKStableSub hU hD S' hS'fd hS'ks
      have hle : S'.map (smD ε π).subtype ≤ S := by
        rw [← hmapV]
        exact Submodule.map_mono hS'le
      have hst : Formalism.MainNotions.S.IsKStableOn ε π (S'.map (smD ε π).subtype) := by
        rintro g hg _ ⟨v, hv, rfl⟩
        obtain ⟨u, hu, hue⟩ := hS'k g hg v hv
        exact ⟨u, hu, hue⟩
      rcases hS.2.2.1 _ hle hst with h0 | h1
      · left
        apply Submodule.map_injective_of_injective (Submodule.injective_subtype (smD ε π))
        rw [h0, Submodule.map_bot]
      · right
        apply Submodule.map_injective_of_injective (Submodule.injective_subtype (smD ε π))
        rw [h1, hmapV]
    have hstd : ReciprocityTheory.ChartRestriction.DS.G2.StdGap ε lam :=
      ⟨hHC.1, h, hgap, by linarith [pow_nonneg hn0 3]⟩
    have hTop := ReciprocityTheory.ChartRestriction.DS.G2.data_closGen_eq_top hstd hU hD hirr
      (fun v _ => part1 v) hVk hDS.2.2.2.1 (fun hb => hw0 ((Submodule.eq_bot_iff V).1 hb w hwV))
    intro x δ hδ
    have hx : x ∈ closGen (smE ε π) V := by
      rw [hTop]
      trivial
    rw [closGen, ← SetLike.mem_coe, Submodule.topologicalClosure_coe, Metric.mem_closure_iff] at hx
    obtain ⟨y, hy, hxy⟩ := hx δ hδ
    obtain ⟨f, hf, rfl⟩ := hy
    refine ⟨f, ?_, ?_⟩
    · rw [SetLike.mem_coe, genSub_eq_iSup_layer hD.glRep hVks,
        Submodule.mem_iSup_of_directed _ (Monotone.directed_le fun k l hkl => layer_mono hkl)] at hf
      obtain ⟨k, hk⟩ := hf
      exact ⟨layer ε (smE ε π) V k, finiteDimensional_layer hVfd k, layer_kStable hD.glRep hVks k, hk⟩
    · rw [← dist_eq_norm]
      exact hxy

end PositivityTheory.RgHe3
