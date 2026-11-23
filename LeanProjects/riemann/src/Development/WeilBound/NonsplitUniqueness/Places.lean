import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.NormCharSplit
import GroundTheory.GlobalFields.KummerTheory.Splitting
import GroundTheory.GlobalFields.TateThesis.DegreeOneDensity

noncomputable section

open NumberField IsDedekindDomain Filter Module GroundTheory.Global GroundTheory.Global.SemiLocal Topology

namespace PositivityTheory.tft.PlacesPf

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem surj_iff_finrank (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    [w.asIdeal.LiesOver v.asIdeal] :
    Function.Surjective (completionMap v w) ↔ finrank (v.adicCompletion F) (w.adicCompletion E) = 1 := by
  rw [Algebra.finrank_eq_one_iff_bijective_algebraMap, algebraMap_completion_eq]
  exact ⟨fun h => ⟨(completionMap v w).injective, h⟩, fun h => h.2⟩

theorem split_iff (v : HeightOneSpectrum (𝓞 F)) :
    UpperTheory.ConvolutionTheory.GM.Split E v ↔ SplitsCompletely E v := by
  rw [splitsCompletely_iff_forall_finrank]
  exact forall_congr' fun w => surj_iff_finrank v w.1

theorem split_infinite [IsGalois F E] :
    {v : HeightOneSpectrum (𝓞 F) | SplitsCompletely E v}.Infinite := by
  intro hfin
  have h1 := hasDirichletDensity_setOf_splitsCompletely F E
  have h0 := hasDirichletDensity_zero_of_finite hfin
  unfold NumberField.Set.HasDirichletDensity at h1 h0
  have h := tendsto_nhds_unique h1 h0
  have hpos : (0 : ℝ) < finrank F E := by exact_mod_cast Module.finrank_pos
  rw [one_div] at h
  exact (inv_ne_zero hpos.ne') h

theorem unr_cofinite : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, UpperTheory.ConvolutionTheory.GM.Unr E v := by
  have hfin := Ideal.finite_factors (differentIdeal_ne_bot (A := 𝓞 F) (B := 𝓞 E))
  refine Filter.eventually_cofinite.2 ((hfin.image fun w => w.under (𝓞 F)).subset ?_)
  intro v hv
  simp only [Set.mem_ofPred_eq, UpperTheory.ConvolutionTheory.GM.Unr, not_forall] at hv
  obtain ⟨w, hw⟩ := hv
  refine ⟨w.1, ?_, ?_⟩
  · exact dvd_differentIdeal_iff.2 hw
  · ext1
    exact w.2.over.symm

theorem unique_of_not_split [IsGalois F E] (hp : (finrank F E).Prime) (v : HeightOneSpectrum (𝓞 F))
    (hv : ¬ UpperTheory.ConvolutionTheory.GM.Split E v) (w w' : PlacesOver E v) : w' = w := by
  rw [split_iff, splitsCompletely_iff_exists_finrank] at hv
  push Not at hv
  have hsum := sum_finrank_eq E v
  rw [Finset.sum_congr rfl (fun u _ => finrank_eq_of_isGalois v u w), Finset.sum_const, smul_eq_mul,
    Finset.card_univ] at hsum
  rw [← hsum] at hp
  rcases Nat.prime_mul_iff.mp hp with ⟨_, h⟩ | ⟨_, h⟩
  · exact absurd h (hv w)
  · exact Fintype.card_le_one_iff.mp h.le w' w

theorem absNorm_eq (w : HeightOneSpectrum (𝓞 E)) :
    Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 F)).asIdeal ^ UpperTheory.ConvolutionTheory.resDeg F w := by
  have : w.asIdeal.LiesOver (w.under (𝓞 F)).asIdeal := ⟨rfl⟩
  have := (w.under (𝓞 F)).isMaximal
  have := w.isMaximal
  rw [Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver w.asIdeal (w.under (𝓞 F)).asIdeal
    (w.under (𝓞 F)).isPrime (w.under (𝓞 F)).ne_bot]
  unfold UpperTheory.ConvolutionTheory.resDeg
  rw [Ideal.inertiaDeg'_eq_inertiaDeg]

theorem liesOver_of_cont (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    (i : v.adicCompletion F →+* w.adicCompletion E) (hi : Continuous i)
    (hc : ∀ x : F, i (algebraMap F _ x) = algebraMap E _ (algebraMap F E x)) :
    w.asIdeal.LiesOver v.asIdeal := by
  have hle : v.asIdeal ≤ w.asIdeal.under (𝓞 F) := by
    intro a ha
    rw [Ideal.under, Ideal.mem_comap]
    set x : v.adicCompletion F := algebraMap F _ (algebraMap (𝓞 F) F a) with hxdef
    have hx : Valued.v x < 1 := by
      rw [hxdef, HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      exact (HeightOneSpectrum.valuation_lt_one_iff_mem v a).2 ha
    have ht := Valued.tendsto_zero_pow_of_v_lt_one hx
    have ht2 : Tendsto (fun n : ℕ => (i x) ^ n) atTop (𝓝 0) := by
      have := (map_zero i ▸ hi.tendsto 0).comp ht
      simpa [Function.comp_def, map_pow] using this
    have hopen := Valued.isOpen_ball (w.adicCompletion E) 1
    obtain ⟨n, hn⟩ := (ht2.eventually (hopen.mem_nhds (by simp))).exists
    rw [Valuation.restrict_lt_one_iff, map_pow] at hn
    have hy : Valued.v (i x) < 1 := by
      by_contra h
      push Not at h
      exact absurd (one_le_pow₀ (n := n) h) (not_le.2 hn)
    rw [hxdef, hc, HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation', ← IsScalarTower.algebraMap_apply (𝓞 F) F E,
      IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 E) E] at hy
    exact (HeightOneSpectrum.valuation_lt_one_iff_mem w _).1 hy
  have hne : w.asIdeal.under (𝓞 F) ≠ ⊤ := (Ideal.IsPrime.under (𝓞 F) w.asIdeal).ne_top
  exact ⟨v.isMaximal.eq_of_le hne hle⟩

theorem cont_iso [IsGalois F E] (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    (i : v.adicCompletion F ≃+* w.adicCompletion E) (hi : Continuous i)
    (hc : ∀ x : F, i (algebraMap F _ x) = algebraMap E _ (algebraMap F E x)) :
    UpperTheory.ConvolutionTheory.GM.Split E v ∧ ∃ u : PlacesOver E v, ∃ h : u.1 = w, ∀ x, i x = h ▸ completionMap v u.1 x := by
  have hlies : w.asIdeal.LiesOver v.asIdeal := liesOver_of_cont v w i.toRingHom hi hc
  have heq : ∀ x, i x = completionMap v w x := by
    have := (HeightOneSpectrum.denseRange_algebraMap F v).equalizer hi (continuous_completionMap v w)
      (funext fun x => by
        simp only [Function.comp_apply, hc, completionMap_algebraMap]
        rw [IsScalarTower.algebraMap_apply F E (w.adicCompletion E)])
    exact congrFun this
  refine ⟨?_, ⟨w, hlies⟩, rfl, heq⟩
  rw [split_iff, splitsCompletely_iff_exists_finrank]
  exact ⟨⟨w, hlies⟩, (surj_iff_finrank v w).1 (fun y => ⟨i.symm y, by rw [← heq]; simp⟩)⟩

end PositivityTheory.tft.PlacesPf

theorem PositivityTheory.tft.places_holds : UpperTheory.ConvolutionTheory.T.Places := by
  intro F E _ _ _ _ _ _ hp
  refine ⟨?_, PositivityTheory.tft.PlacesPf.unr_cofinite, fun v => nonempty_placesOver E v,
    PositivityTheory.tft.PlacesPf.unique_of_not_split hp, PositivityTheory.tft.PlacesPf.absNorm_eq,
    fun v w i hi hc => PositivityTheory.tft.PlacesPf.cont_iso v w i hi hc⟩
  have := PositivityTheory.tft.PlacesPf.split_infinite (F := F) (E := E)
  have hset : {v : HeightOneSpectrum (𝓞 F) | UpperTheory.ConvolutionTheory.GM.Split E v} = {v | SplitsCompletely E v} :=
    Set.ext fun v => PositivityTheory.tft.PlacesPf.split_iff v
  rw [hset]
  exact this
