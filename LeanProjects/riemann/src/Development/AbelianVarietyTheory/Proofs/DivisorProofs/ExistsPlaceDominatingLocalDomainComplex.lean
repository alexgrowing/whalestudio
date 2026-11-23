import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EssFiniteTypeOfLocalizationFiniteTypeComplex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrLocalizationOfMinimalPrimeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalFiniteTypeSubringLeValuationSubringAStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.DvrDom

theorem exists_fractions_of_essFiniteType : ∀ {κ : Type} [Field κ] [Algebra ℂ κ] (O : Subring κ) (hc : ∀ a : ℂ, algebraMap ℂ κ a ∈ O), ((algebraMap ℂ κ).codRestrict O hc).EssFiniteType → ∃ G : Finset κ, (∀ x ∈ G, x ∈ O) ∧ ∀ o ∈ O, ∃ b ∈ Algebra.adjoin ℂ (G : Set κ), ∃ d ∈ Algebra.adjoin ℂ (G : Set κ), d ≠ 0 ∧ d⁻¹ ∈ O ∧ o = b / d := by
  classical
  intro κ _ _ O hc h
  letI : Algebra ℂ O := ((algebraMap ℂ κ).codRestrict O hc).toAlgebra
  have h' : Algebra.EssFiniteType ℂ O := h
  obtain ⟨s, hs⟩ := h'.cond
  refine ⟨s.image (fun x : O => (x : κ)), ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨y, -, rfl⟩ := hx
    exact y.2
  have key : ∀ x ∈ Algebra.adjoin ℂ (s : Set O),
      ((x : O) : κ) ∈ Algebra.adjoin ℂ ((s.image (fun x : O => (x : κ)) : Finset κ) : Set κ) := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      apply Algebra.subset_adjoin
      rw [Finset.coe_image]
      exact ⟨x, hx, rfl⟩
    | algebraMap r => exact Subalgebra.algebraMap_mem _ r
    | add x y _ _ hx hy => simpa using Subalgebra.add_mem _ hx hy
    | mul x y _ _ hx hy => simpa using Subalgebra.mul_mem _ hx hy
  intro v hv
  obtain ⟨⟨a, m⟩, hm⟩ := IsLocalization.surj
    (Submonoid.comap (algebraMap (↥(Algebra.adjoin ℂ (s : Set O))) O) (IsUnit.submonoid O)) (⟨v, hv⟩ : O)
  have hu : IsUnit ((m : Algebra.adjoin ℂ (s : Set O)) : O) := m.2
  obtain ⟨u, hu'⟩ := hu
  have hinv : (((m : Algebra.adjoin ℂ (s : Set O)) : O) : κ) * (((u⁻¹ : Oˣ) : O) : κ) = 1 := by
    rw [← hu']
    change (((u : O) * ((u⁻¹ : Oˣ) : O) : O) : κ) = ((1 : O) : κ)
    rw [u.mul_inv]
  have hd0 : (((m : Algebra.adjoin ℂ (s : Set O)) : O) : κ) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hinv
    exact zero_ne_one hinv
  have hmL := congrArg (fun z : O => (z : κ)) hm
  simp only at hmL
  refine ⟨((a : O) : κ), key _ a.2, (((m : Algebra.adjoin ℂ (s : Set O)) : O) : κ),
    key _ (m : Algebra.adjoin ℂ (s : Set O)).2, hd0, ?_, ?_⟩
  · rw [inv_eq_of_mul_eq_one_right hinv]
    exact ((u⁻¹ : Oˣ) : O).2
  · rw [eq_div_iff hd0]
    simpa using hmL

theorem exists_minimal_prime_le : ∀ {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] (P : Ideal R) [P.IsPrime] (a : R), a ≠ 0 → a ∈ P → ∃ Q : Ideal R, Q.IsPrime ∧ a ∈ Q ∧ Q ≤ P ∧ Q ≠ ⊥ ∧ ∀ p : Ideal R, p.IsPrime → p ≠ ⊥ → p ≤ Q → p = Q := by
  intro R _ _ _ P _ a ha haP
  have hle : Ideal.span {a} ≤ P := (Ideal.span_singleton_le_iff_mem P).2 haP
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_minimalPrimes_le hle
  have hQp : Q.IsPrime := hQ.1.1
  have haQ : a ∈ Q := hQ.1.2 (Ideal.mem_span_singleton_self a)
  have hQ0 : Q ≠ ⊥ := fun h => ha (by rw [h] at haQ; exact (Ideal.mem_bot).1 haQ)
  have hht : Q.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ Q hQ
  refine ⟨Q, hQp, haQ, hQP, hQ0, fun p hp hp0 hpQ => ?_⟩
  by_contra hne
  have hlt : p < Q := lt_of_le_of_ne hpQ hne
  haveI := hp
  haveI := hQp
  have h1 : p.height + 1 ≤ Q.height := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  have hp1 : 1 ≤ p.height :=
    Order.one_le_iff_ne_zero.mpr (fun h => hp0 (Ideal.height_eq_zero_iff_eq_bot.1 h))
  have h2 : (1 : ℕ∞) + 1 ≤ 1 := (add_le_add_left hp1 1).trans (h1.trans hht)
  exact absurd h2 (by decide)

theorem exists_place_dominating : ∀ {κ : Type} [Field κ] [Algebra ℂ κ] (O : Subring κ) (hO : IsLocModel (algebraMap ℂ κ) O), letI := hO.isLocalRing;
  ¬ IsField O → ∃ F : Place (algebraMap ℂ κ), F.Contains O ∧ ∀ f : O, f ∈ IsLocalRing.maximalIdeal O → (f : κ) ≠ 0 → 0 < F.ord f := by
  intro κ _ _ O hO
  letI := hO.isLocalRing
  intro hnf
  classical
  obtain ⟨G, hGO, hGfrac⟩ := exists_fractions_of_essFiniteType O hO.const_mem hO.essFiniteType
  letI : Algebra ℂ O := ((algebraMap ℂ κ).codRestrict O hO.const_mem).toAlgebra
  haveI : Algebra.EssFiniteType ℂ O := hO.essFiniteType
  haveI : IsNoetherianRing O := Algebra.EssFiniteType.isNoetherianRing ℂ O
  obtain ⟨Y, hY⟩ := (IsNoetherian.noetherian (IsLocalRing.maximalIdeal O) :
    (IsLocalRing.maximalIdeal O).FG)

  obtain ⟨V, hOV⟩ := (LocalSubring.mk O).exists_le_valuationSubring
  obtain ⟨hle, hloc⟩ := (LocalSubring.le_def).1 hOV
  have hOV' : ∀ x ∈ O, x ∈ V := fun x hx => hle hx
  have hVnu : ∀ x : O, x ∈ IsLocalRing.maximalIdeal O → ∀ hx : (x : κ) ∈ V,
      (⟨x, hx⟩ : V) ∈ IsLocalRing.maximalIdeal V := by
    intro x hxm hx
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hxm
    exact hxm (hloc.map_nonunit x hu)

  have hm0 : IsLocalRing.maximalIdeal O ≠ ⊥ := fun h =>
    hnf ((IsLocalRing.isField_iff_maximalIdeal_eq).2 h)
  let Y' : Finset O := Y.filter (fun y : O => (y : κ) ≠ 0)
  have hY'ne : Y'.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    apply hm0
    rw [← hY, Submodule.span_eq_bot]
    intro y hy
    by_contra hy0
    have : y ∈ Y' := Finset.mem_filter.2 ⟨hy, fun h => hy0 (Subtype.ext h)⟩
    rw [hne] at this
    exact absurd this (Finset.notMem_empty _)
  obtain ⟨a, haY', hamax⟩ := Y'.exists_max_image (fun y : O => V.valuation (y : κ)) hY'ne
  obtain ⟨haY, ha0⟩ := Finset.mem_filter.1 haY'
  have hdivV : ∀ y ∈ Y, (y : κ) / a ∈ V := by
    intro y hy
    by_cases hy0 : (y : κ) = 0
    · rw [hy0, zero_div]; exact V.zero_mem
    rw [← ValuationSubring.valuation_le_one_iff, map_div₀]
    have h1 := hamax y (Finset.mem_filter.2 ⟨hy, hy0⟩)
    have h2 : V.valuation (a : κ) ≠ 0 := (Valuation.ne_zero_iff _).2 ha0
    exact (div_le_one₀ (zero_lt_iff.2 h2)).2 h1

  let T : Finset κ := G ∪ Y.image (fun y : O => (y : κ)) ∪ Y.image (fun y : O => (y : κ) / a)
  have hTV : ∀ x ∈ T, x ∈ V := by
    intro x hx
    simp only [T, Finset.mem_union, Finset.mem_image] at hx
    rcases hx with (hx | ⟨y, -, rfl⟩) | ⟨y, hy, rfl⟩
    · exact hOV' x (hGO x hx)
    · exact hOV' _ y.2
    · exact hdivV y hy
  have hGT : Algebra.adjoin ℂ (G : Set κ) ≤ Algebra.adjoin ℂ (T : Set κ) :=
    Algebra.adjoin_mono (by intro x hx; simp [T, Finset.mem_coe.1 hx])
  have hfracT : ∀ f : κ, ∃ u ∈ Algebra.adjoin ℂ (T : Set κ), ∃ v ∈ Algebra.adjoin ℂ (T : Set κ),
      v ≠ 0 ∧ f * v = u := by
    intro f
    obtain ⟨x, hx, z, hz, hz0, hfz⟩ := hO.frac f
    obtain ⟨b, hb, d, hd, hd0, -, rfl⟩ := hGfrac x hx
    obtain ⟨b', hb', d', hd', hd0', -, rfl⟩ := hGfrac z hz
    have hb0' : b' ≠ 0 := by rintro rfl; exact hz0 (zero_div _)
    refine ⟨b * d', Subalgebra.mul_mem _ (hGT hb) (hGT hd'), b' * d,
      Subalgebra.mul_mem _ (hGT hb') (hGT hd), mul_ne_zero hb0' hd0, ?_⟩
    field_simp at hfz
    linear_combination hfz
  have hcV : ∀ z : ℂ, algebraMap ℂ κ z ∈ V := fun z => hOV' _ (hO.const_mem z)
  obtain ⟨R, hcR, hft, hTR, hRV, hRn, hRi, hRf⟩ := GlobalTheory.T.exists_normal_finiteType_subring_le_valuationSubring' V T hcV hTV hfracT
  haveI := hRn
  haveI := hRi
  haveI := hRf
  have hadjR : ∀ x ∈ Algebra.adjoin ℂ (T : Set κ), x ∈ R := by
    let R' : Subalgebra ℂ κ := { R with algebraMap_mem' := hcR }
    have : Algebra.adjoin ℂ (T : Set κ) ≤ R' := Algebra.adjoin_le (fun x hx => hTR x hx)
    exact fun x hx => this hx

  let ι : R →+* V :=
    { toFun := fun r => ⟨r, hRV r.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let P : Ideal R := (IsLocalRing.maximalIdeal V).comap ι
  haveI : P.IsPrime := Ideal.comap_isPrime _ _
  have haT : (a : κ) ∈ T := by simp [T, haY]
  let a' : R := ⟨a, hTR _ haT⟩
  have ha'0 : a' ≠ 0 := fun h => ha0 (congrArg Subtype.val h)
  have ha'P : a' ∈ P := hVnu a (hY ▸ Submodule.subset_span haY) _
  obtain ⟨Q, hQp, haQ, hQP, hQ0, hmin⟩ := exists_minimal_prime_le P a' ha'0 ha'P
  haveI := hQp
  obtain ⟨W, hWd, hRW, hinvW, hninvW, hWfrac⟩ := GlobalTheory.T.exists_dvr_localization_of_minimal_prime' R Q hQ0 hmin

  have hcW : ∀ z : ℂ, algebraMap ℂ κ z ∈ W := fun z => hRW ⟨_, hcR z⟩
  have hWft : ((algebraMap ℂ κ).codRestrict W hcW).EssFiniteType :=
    GlobalTheory.EssFiniteDescent.essFiniteType_of_eq_div κ (algebraMap ℂ κ) R hcR W hcW
      (fun x hx => hRW ⟨x, hx⟩) hft (fun e he => by
        obtain ⟨b, s, hs, rfl⟩ := hWfrac e he
        exact ⟨b, b.2, s, s.2, hinvW s hs, rfl⟩)
  let F : Place (algebraMap ℂ κ) := ⟨W, hcW, hWd, hWft⟩
  have hOW : ∀ o ∈ O, o ∈ W := by
    intro o ho
    obtain ⟨b, hb, d, hd, hd0, hdi, rfl⟩ := hGfrac o ho
    let d' : R := ⟨d, hadjR _ (hGT hd)⟩
    have hd'Q : d' ∉ Q := by
      intro hdQ
      have hm : ι d' ∈ IsLocalRing.maximalIdeal V := hQP hdQ
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hm
      apply hm
      exact IsUnit.of_mul_eq_one (⟨d⁻¹, hOV' _ hdi⟩ : V) (Subtype.ext (mul_inv_cancel₀ hd0))
    rw [div_eq_mul_inv]
    exact mul_mem (hRW ⟨b, hadjR _ (hGT hb)⟩) (hinvW d' hd'Q)
  refine ⟨F, hOW, ?_⟩
  intro f hf hf0
  have hspan : ∀ x ∈ Submodule.span O (Y : Set O), ∃ w ∈ W, ((x : O) : κ) = a * w := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      refine ⟨(y : κ) / a, hRW ⟨_, hTR _ ?_⟩, ?_⟩
      · simp only [T, Finset.mem_union, Finset.mem_image]
        exact Or.inr ⟨y, hy, rfl⟩
      · field_simp
    | zero => exact ⟨0, zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨w, hw, ex⟩ := hx
      obtain ⟨w', hw', ey⟩ := hy
      exact ⟨w + w', add_mem hw hw', by push_cast; rw [ex, ey]; ring⟩
    | smul c x _ hx =>
      obtain ⟨w, hw, ex⟩ := hx
      refine ⟨c * w, mul_mem (hOW _ c.2) hw, ?_⟩
      rw [smul_eq_mul, Subring.coe_mul, ex]; ring
  rw [← hY] at hf
  obtain ⟨w, hw, efw⟩ := hspan f hf
  have hw0 : w ≠ 0 := by rintro rfl; exact hf0 (by rw [efw, mul_zero])
  have haW : (a : κ) ∈ W := hRW a'
  have hainv : (a : κ)⁻¹ ∉ W := hninvW a' haQ ha'0
  have h1 : 0 ≤ F.ord (a : κ) := (F.ord_nonneg_iff ha0).2 haW
  have h2 : ¬ 0 ≤ F.ord ((a : κ)⁻¹) := fun h => hainv ((F.ord_nonneg_iff (inv_ne_zero ha0)).1 h)
  have h3 : 0 ≤ F.ord w := (F.ord_nonneg_iff hw0).2 hw
  rw [F.ord_inv] at h2
  rw [efw, F.ord_mul ha0 hw0]
  omega

end GlobalTheory.DvrDom
