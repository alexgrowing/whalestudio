import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedConjugatePlaceUniformiser
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsComplexConjIsometryInertCompletion

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory.InertPlaceConj

open GlobalTheory.SelfDualGenus

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem isInertAt_of_not_split (w : HeightOneSpectrum (𝓞 E))
    (hu : Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) (hs : ¬ IsSplitAt w) :
    Formalism.UG.IsInertAt (maximalRealSubfield E) E (w.under (𝓞 (maximalRealSubfield E))) w := by
  classical
  haveI := w.isPrime
  set v := w.under (𝓞 (maximalRealSubfield E)) with hv
  have hva : v.asIdeal = w.asIdeal.under (𝓞 (maximalRealSubfield E)) := rfl
  have hinj : Function.Injective (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) :=
    FaithfulSMul.algebraMap_injective _ _
  unfold Formalism.UG.IsInertAt
  rw [hva]
  have hle : (w.asIdeal.under (𝓞 (maximalRealSubfield E))).map
      (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) ≤ w.asIdeal := Ideal.map_comap_le
  have h1 : Ideal.ramificationIdx' (w.asIdeal.under (𝓞 (maximalRealSubfield E))) w.asIdeal = 1 := by
    letI := Localization.AtPrime.algebraOfLiesOver (w.asIdeal.under (𝓞 (maximalRealSubfield E))) w.asIdeal
    exact (Ideal.IsDedekindDomain.ramificationIdx'_eq_one_iff w.ne_bot hle).2
      ((Algebra.isUnramifiedAt_iff_map_eq (𝓞 (maximalRealSubfield E))
        (w.asIdeal.under (𝓞 (maximalRealSubfield E))) w.asIdeal).1 hu).2
  have h2 : ¬ (w.asIdeal.under (𝓞 (maximalRealSubfield E))).map
      (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) ≤ w.asIdeal ^ 2 :=
    fun h => (Ideal.ramificationIdx'_ne_one_iff hle).2 h h1
  set I := Ideal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E))
    (w.asIdeal.under (𝓞 (maximalRealSubfield E))) with hI
  have hI0 : I ≠ ⊥ := by
    rw [hI, Ne, Ideal.map_eq_bot_iff_of_injective hinj]
    exact v.ne_bot
  have hfac : ∀ p ∈ UniqueFactorizationMonoid.normalizedFactors I, p = w.asIdeal := by
    intro p hp
    obtain ⟨hpp, hpl⟩ := (Ideal.mem_normalizedFactors_iff hI0).1 hp
    have hp0 : p ≠ ⊥ := fun h0 => hI0 (le_bot_iff.1 (h0 ▸ hpl))
    let u : HeightOneSpectrum (𝓞 E) := ⟨p, hpp, hp0⟩
    have hu' : u.under (𝓞 (maximalRealSubfield E)) = v := by
      ext1
      exact (v.isMaximal.eq_of_le (Ideal.comap_ne_top _ hpp.ne_top)
        (Ideal.map_le_iff_le_comap.1 hpl)).symm
    by_contra hne
    exact hs ⟨u, fun h => hne (congrArg HeightOneSpectrum.asIdeal h), hu'⟩
  obtain ⟨n, hn⟩ : ∃ n, I = w.asIdeal ^ n := by
    refine ⟨Multiset.card (UniqueFactorizationMonoid.normalizedFactors I), ?_⟩
    conv_lhs => rw [← Ideal.prod_normalizedFactors_eq_self hI0]
    rw [Multiset.eq_replicate_card.2 hfac, Multiset.prod_replicate, Multiset.card_replicate]
  rcases n with _ | _ | n
  · exfalso
    rw [hn, pow_zero, Ideal.one_eq_top, top_le_iff] at hle
    exact w.isPrime.ne_top hle
  · simpa using hn
  · exact absurd (hn ▸ Ideal.pow_le_pow_right (by omega)) h2

theorem exists_sub_conj_notMem_of_inert (w : HeightOneSpectrum (𝓞 E))
    (h : Formalism.UG.IsInertAt (maximalRealSubfield E) E (w.under (𝓞 (maximalRealSubfield E))) w) :
    ∃ x : 𝓞 E, x - IsCMField.ringOfIntegersComplexConj E x ∉ w.asIdeal := by
  set v := w.under (𝓞 (maximalRealSubfield E)) with hv
  have h' : Ideal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) v.asIdeal = w.asIdeal := h
  have := v.isPrime
  have := w.isPrime
  have : w.asIdeal.LiesOver v.asIdeal := ⟨rfl⟩
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn (G := E ≃ₐ[maximalRealSubfield E] E) v.asIdeal w.asIdeal
  have hsq : ¬ Ideal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) v.asIdeal ≤ w.asIdeal ^ 2 := by
    rw [h']
    exact (Ideal.pow_lt_self _ w.ne_bot w.isPrime.ne_top 2 le_rfl).not_ge
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal w.asIdeal (E ≃ₐ[maximalRealSubfield E] E),
    ← Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.asIdeal v.ne_bot,
    not_ne_iff.1 (mt (Ideal.ramificationIdx'_ne_one_iff (le_of_eq h')).1 hsq)] at hcard
  by_contra hn
  push_neg at hn
  have hs : IsCMField.complexConj E ∈ w.asIdeal.inertia (E ≃ₐ[maximalRealSubfield E] E) :=
    AddSubgroup.mem_inertia.2 fun x => by
      have := w.asIdeal.neg_mem (hn x)
      rw [neg_sub] at this
      exact this
  rw [Subgroup.eq_bot_of_card_eq _ hcard, Subgroup.mem_bot] at hs
  exact IsCMField.complexConj_ne_one E hs

theorem exists_isUnramInv_of_inert (w : HeightOneSpectrum (𝓞 E))
    (h : Formalism.UG.IsInertAt (maximalRealSubfield E) E (w.under (𝓞 (maximalRealSubfield E))) w) :
    ∃ (s : w.adicCompletion E →+* w.adicCompletion E) (ϖ : w.adicCompletion E),
      (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) ∧
      IsUnramInv ϖ s (Ideal.absNorm (w.under (𝓞 (maximalRealSubfield E))).asIdeal) := by
  set v := w.under (𝓞 (maximalRealSubfield E)) with hv
  have h' : Ideal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) v.asIdeal = w.asIdeal := h
  have hc : Mem.Chr.ConjPl (IsCMField.complexConj E).toRingEquiv w w := by
    rw [Mem.Chr.conjPl_iff_mem]
    intro x y hxy
    have e : y = IsCMField.ringOfIntegersComplexConj E x := RingOfIntegers.ext hxy
    rw [e]
    refine ⟨GlobalTheory.InertConj.conj_mem_of_inert h, fun hx => ?_⟩
    have h2 := GlobalTheory.InertConj.conj_mem_of_inert h hx
    have e2 : IsCMField.ringOfIntegersComplexConj E (IsCMField.ringOfIntegersComplexConj E x) = x := by
      ext; simp
    rwa [e2] at h2
  obtain ⟨σ, σ1, σ2, σ3⟩ := UnramCompletion.exists_ringEquiv w _ hc
  have σ2' : ∀ x : E, σ (algebraMap E (w.adicCompletion E) x) =
      algebraMap E (w.adicCompletion E) (IsCMField.complexConj E x) := σ2
  obtain ⟨s, hs, hs2⟩ : ∃ s ∈ v.asIdeal,
      algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s ∉ w.asIdeal ^ 2 := by
    by_contra hn
    push_neg at hn
    have h1 : w.asIdeal ≤ w.asIdeal ^ 2 := by
      conv_lhs => rw [← h']
      exact Ideal.map_le_iff_le_comap.2 hn
    exact (Ideal.pow_lt_self _ w.ne_bot w.isPrime.ne_top 2 le_rfl).not_ge h1
  have hs1 : algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s ∈ w.asIdeal :=
    h' ▸ Ideal.mem_map_of_mem _ hs
  have hval : ∀ a : 𝓞 E, Valued.v (algebraMap E (w.adicCompletion E) (a : E)) =
      w.valuation E (algebraMap (𝓞 E) E a) := fun a =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
  have hinv : ∀ x, σ (σ x) = x := by
    intro x
    refine congrFun (UnramCompletion.ringHom_ext_of_continuous w (f := fun x => σ (σ x))
      (σ1.comp σ1) continuous_id fun k => ?_) x
    simp [σ2']
  have hres : ∃ x, Valued.v x ≤ 1 ∧ Valued.v ((σ : w.adicCompletion E →+* w.adicCompletion E) x - x) = 1 := by
    obtain ⟨x, hx⟩ := exists_sub_conj_notMem_of_inert w h
    refine ⟨algebraMap E _ (x : E), ?_, ?_⟩
    · rw [hval]; exact w.valuation_le_one x
    · change Valued.v (σ _ - _) = 1
      rw [Valuation.map_sub_swap, σ2', ← map_sub]
      exact (hval (x - IsCMField.ringOfIntegersComplexConj E x)).trans
        ((HeightOneSpectrum.valuation_eq_one_iff_notMem w).2 hx)
  have hfix : (σ : w.adicCompletion E →+* w.adicCompletion E)
      (algebraMap E _ (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s : E)) =
      algebraMap E _ (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s : E) := by
    change σ _ = _
    rw [σ2']
    congr 1
    exact IsCMField.complexConj_apply_eq_self E (s : maximalRealSubfield E)
  have hunif : IsUnifV E w (algebraMap E _ (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s : E)) := by
    unfold IsUnifV
    rw [hval, HeightOneSpectrum.valuation_of_algebraMap]
    exact UnramCompletion.intValuation_eq_of_notMem_sq w hs1 hs2
  refine ⟨σ, _, σ2', hinv, σ3, hfix, hunif, ?_, ?_, ?_⟩
  · obtain ⟨x, hx1, hx2⟩ := hres
    exact ⟨x, hx1, hx2⟩
  · have a : Ideal.absNorm v.asIdeal ≠ 1 := fun h => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
    have b : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
    omega
  · have hN : Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal ^ 2 := by
      rw [← h', Ideal.absNorm_algebraMap,
        ← Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E]
      congr 1
      exact (Algebra.IsAlgebraic.finrank_of_isFractionRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)
        (𝓞 E) E).symm
    rw [← hN]
    exact Formalism.UG.P.tjcosets_card_residue w

theorem exists_conj_isUnramInv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)),
    Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal → ¬ IsSplitAt w →
    ∃ (s : w.adicCompletion E →+* w.adicCompletion E) (ϖ : w.adicCompletion E) (q : ℕ),
      (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) ∧ IsUnramInv ϖ s q := by
  intro E _ _ _ w hu hs
  obtain ⟨s, ϖ, h1, h2⟩ := exists_isUnramInv_of_inert w (isInertAt_of_not_split w hu hs)
  exact ⟨s, ϖ, _, h1, h2⟩

end GlobalTheory.InertPlaceConj
