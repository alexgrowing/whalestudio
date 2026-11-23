import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogAbsEEqZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdeleCharacterEqOneIntegralUnitsUnramifiedAdelic
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.PlaceAbove

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem eq_one_of_isCompact {G : Type} [Group G] [TopologicalSpace G] (f : G →* ℝ≥0) (hf : Continuous f)
    (H : Subgroup G) (hH : IsCompact (H : Set G)) {x : G} (hx : x ∈ H) : f x = 1 := by
  obtain ⟨C, hC⟩ := (hH.image hf).bddAbove
  have key : ∀ m ∈ H, f m ≤ 1 := fun m hm => by
    by_contra h
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt C (not_le.1 h)
    exact not_le.2 hk (by rw [← map_pow]; exact hC ⟨_, pow_mem hm k, rfl⟩)
  refine le_antisymm (key x hx) ?_
  have h1 := key _ (inv_mem hx)
  calc (1 : ℝ≥0) = f x * f x⁻¹ := by rw [← map_mul, mul_inv_cancel, map_one]
    _ ≤ f x * 1 := by gcongr
    _ = _ := mul_one _

theorem valued_eq_one (w : HeightOneSpectrum (𝓞 E)) (a : 𝓞 E) (ha : a ∉ w.asIdeal) :
    Valued.v (algebraMap E (w.adicCompletion E) (a : E)) = 1 := by
  show Valued.v (((a : E)) : w.adicCompletion E) = _
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]
  exact (HeightOneSpectrum.intValuation_eq_one_iff).mpr ha

theorem absE_locIdele_of_unit (w : HeightOneSpectrum (𝓞 E)) (u : (w.adicCompletion E)ˣ)
    (hu : (u : w.adicCompletion E) ∈ w.adicCompletionIntegers E)
    (hu' : ((u⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) ∈ w.adicCompletionIntegers E) :
    absE F E (locIdele F w u) = 1 := by
  let S : Submonoid (w.adicCompletion E) := (w.adicCompletionIntegers E).toSubring.toSubmonoid
  have hS : IsCompact (S : Set (w.adicCompletion E)) :=
    isCompact_iff_compactSpace.2 (GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers E w)
  exact eq_one_of_isCompact ((absE F E).comp (locIdele F w))
    (GlobalTheory.Doubling.continuous_absE.comp (continuous_locIdele w)) S.units (Submonoid.units_isCompact hS)
    ((Submonoid.mem_units_iff _ _).2 ⟨hu, hu'⟩)

end GlobalTheory.PlaceAbove

namespace GlobalTheory.PlaceAbove

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_under_eq' (v : HeightOneSpectrum (𝓞 F)) : ∃ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v := by
  have := v.isPrime
  obtain ⟨Q, hQ, hl⟩ := (Ideal.nonempty_primesOver v.asIdeal (S := 𝓞 E)).some
  exact ⟨⟨Q, hQ, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, HeightOneSpectrum.ext hl.over.symm⟩

theorem exists_sep (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) :
    ∃ a : 𝓞 E, a ≠ 0 ∧ a ∈ w.asIdeal ∧
      ∀ w' : HeightOneSpectrum (𝓞 E), w'.under (𝓞 F) = v → w' ≠ w → a ∉ w'.asIdeal := by
  classical
  obtain ⟨π, hπ, hπ2⟩ : ∃ π ∈ w.asIdeal, π ∉ w.asIdeal ^ 2 := by
    have := Ideal.pow_right_strictAnti w.asIdeal w.ne_bot w.isPrime.ne_top (show 1 < 2 by norm_num)
    simp only [pow_one] at this
    obtain ⟨π, h1, h2⟩ := Set.exists_of_ssubset this
    exact ⟨π, h1, h2⟩
  let s : Finset (HeightOneSpectrum (𝓞 E)) := insert w (Formalism.L2.Host.finite_aboveF (L := E) F v).toFinset
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := s) (fun i => i.asIdeal)
    (fun i => if i = w then 2 else 1) (fun i _ => i.prime) (fun i _ j _ hij h => hij (HeightOneSpectrum.ext h))
    (fun i => if i.1 = w then π else 1)
  have hw := hy w (Finset.mem_insert_self _ _)
  simp only [if_pos rfl] at hw
  have hyw : y ∈ w.asIdeal := by
    have := Ideal.pow_le_self two_ne_zero hw
    simpa using w.asIdeal.add_mem this hπ
  refine ⟨y, fun h0 => hπ2 ?_, hyw, fun w' hw' hne hyw' => ?_⟩
  · rw [h0, zero_sub] at hw; simpa using hw
  · have h' := hy w' (Finset.mem_insert_of_mem ((Formalism.L2.Host.finite_aboveF (L := E) F v).mem_toFinset.2 hw'))
    simp only [if_neg hne, pow_one] at h'
    exact w'.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using w'.asIdeal.sub_mem hyw' h'))

end GlobalTheory.PlaceAbove

namespace GlobalTheory.PlaceAbove

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem nnnorm_lt_one (v : HeightOneSpectrum (𝓞 F)) (b : 𝓞 F) (hb : b ∈ v.asIdeal) :
    ‖algebraMap F (Fv F v) (b : F)‖₊ < 1 := by
  have h : Valued.v (algebraMap F (Fv F v) (b : F)) < 1 := by
    show Valued.v (((b : F)) : v.adicCompletion F) < 1
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]
    exact (HeightOneSpectrum.intValuation_lt_one_iff_mem _ _).2 hb
  have := Valued.toNormedField.norm_lt_one_iff.2 h
  exact_mod_cast this

theorem exists_absE_locIdele_ne_one (w : HeightOneSpectrum (𝓞 E)) :
    ∃ x : (w.adicCompletion E)ˣ, absE F E (locIdele F w x) ≠ 1 := by
  classical
  obtain ⟨a, ha0, haw, hao⟩ := exists_sep (w.under (𝓞 F)) w
  have hE0 : (a : E) ≠ 0 := fun h => ha0 (by exact_mod_cast h)
  let y : (Fv F (w.under (𝓞 F)) ⊗[F] E)ˣ :=
    Units.map (inclR (F := F) (Fv F (w.under (𝓞 F)))).toMonoidHom (Units.mk0 (a : E) hE0)
  have hval : ∀ (w' : HeightOneSpectrum (𝓞 E)) (h : w'.under (𝓞 F) = w.under (𝓞 F)),
      ((Units.map (toCompl h).toMonoidHom y : (w'.adicCompletion E)ˣ) : w'.adicCompletion E) =
        algebraMap E _ (a : E) := by
    intro w' h
    show toCompl h ((1 : Fv F (w.under (𝓞 F))) ⊗ₜ[F] (a : E)) = _
    rw [toCompl_tmul, map_one, one_mul]
  have key := congrArg (absE F E) (ideleAt_eq_prod_locIdele (w.under (𝓞 F)) y)
  rw [GlobalTheory.Doubling.absE_ideleAt, map_prod] at key
  have hmem : w ∈ (Formalism.L2.Host.finite_aboveF (L := E) F (w.under (𝓞 F))).toFinset :=
    (Formalism.L2.Host.finite_aboveF (L := E) F (w.under (𝓞 F))).mem_toFinset.2 rfl
  rw [Finset.prod_eq_single_of_mem ⟨w, hmem⟩ (Finset.mem_attach _ _) (fun b _ hb => by
    have hbv : b.1.under (𝓞 F) = w.under (𝓞 F) :=
      (Formalism.L2.Host.finite_aboveF (L := E) F (w.under (𝓞 F))).mem_toFinset.1 b.2
    have hne : b.1 ≠ w := fun e => hb (Subtype.ext e)
    have hv1 := valued_eq_one b.1 a (hao b.1 hbv hne)
    refine absE_locIdele_of_unit b.1 _ ?_ ?_
    · rw [hval]
      exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hv1.le
    · rw [Units.val_inv_eq_inv_val, hval]
      refine (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 ?_
      rw [map_inv₀, hv1, inv_one])] at key
  refine ⟨Units.map (toCompl (rfl : w.under (𝓞 F) = w.under (𝓞 F))).toMonoidHom y, ?_⟩
  have key' : absE F E (locIdele F w (Units.map (toCompl (rfl : w.under (𝓞 F) = w.under (𝓞 F))).toMonoidHom y)) =
      GlobalTheory.Doubling.absEv F E (w.under (𝓞 F)) y := key.symm
  rw [key']
  refine ne_of_lt ?_
  rw [GlobalTheory.Doubling.absEv_apply]
  show ‖Algebra.norm (Fv F (w.under (𝓞 F))) (inclR (F := F) (Fv F (w.under (𝓞 F))) (a : E))‖₊ < 1
  rw [GlobalTheory.Doubling.norm_inclR, ← Algebra.algebraMap_intNorm (L := E) (A := 𝓞 F) (B := 𝓞 E) a]
  refine nnnorm_lt_one _ _ ?_
  have h1 := Ideal.spanNorm_le_comap (𝓞 F) w.asIdeal (Ideal.intNorm_mem_spanNorm (𝓞 F) haw)
  rw [HeightOneSpectrum.under_asIdeal, Ideal.under_def]
  exact h1

end GlobalTheory.PlaceAbove

open GlobalTheory.PlaceAbove in

theorem GlobalTheory.PlaceAbove.places : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    (∀ v : HeightOneSpectrum (𝓞 F), ∃ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v) ∧
      ∀ w : HeightOneSpectrum (𝓞 E), ∃ x : (w.adicCompletion E)ˣ, absE F E (locIdele F w x) ≠ 1 :=
  fun _ _ _ _ _ _ _ => ⟨exists_under_eq', exists_absE_locIdele_ne_one⟩
