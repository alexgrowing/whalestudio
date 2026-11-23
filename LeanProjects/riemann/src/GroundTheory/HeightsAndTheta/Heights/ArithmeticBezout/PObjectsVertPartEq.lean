import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LengthLocalizedModuleQuotient
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChowDegreeGeoNum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial NumberField VerticalPartMultiplicity
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk)

theorem finsum_finset_sum_comm {α β : Type*} (T : Finset α) (g : β → α → ℝ)
    (h : ∀ a ∈ T, (Function.support fun b => g b a).Finite) :
    ∑ᶠ b, ∑ a ∈ T, g b a = ∑ a ∈ T, ∑ᶠ b, g b a := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha ih =>
    have h' : ∀ a' ∈ T, (Function.support fun b => g b a').Finite :=
      fun a' h'' => h a' (Finset.mem_insert_of_mem h'')
    simp_rw [Finset.sum_insert ha]
    rw [finsum_add_distrib (h a (Finset.mem_insert_self _ _)), ih h']
    refine (T.finite_toSet.biUnion fun a' h'' => h' a' h'').subset ?_
    intro b hb
    obtain ⟨a', ha', hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hb
    exact Set.mem_biUnion ha' hne

theorem isMultiHomog_linearForm {n : ℕ} (u : Fin n → ℤ) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (IndefiniteRowSideFullHecke.ArithBezout.linForm u) (fun _ => 1) := by
  classical
  intro m hm k
  obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hm)
  rw [ReciprocityTheory.ChartRestriction.G.Geo.Xc, C_mul_X_eq_monomial] at hi
  have hm' := MvPolynomial.support_monomial_subset hi
  rw [Finset.mem_singleton] at hm'
  subst hm'
  cases k
  simp [Finsupp.single_apply]

theorem C_charOf_mem {n : ℕ} (W : Ideal (MRing (PBlk n))) :
    (C ((ReciprocityTheory.ChartRestriction.G.Geo.charOf W : ℕ) : ℤ) : MRing (PBlk n)) ∈ W := by
  have hg := Submodule.IsPrincipal.generator_mem (W.comap (C : ℤ →+* MRing (PBlk n)))
  obtain ⟨c, hc⟩ : Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* MRing (PBlk n))) ∣
      ((ReciprocityTheory.ChartRestriction.G.Geo.charOf W : ℕ) : ℤ) := Int.dvd_natAbs.mpr dvd_rfl
  have : ((ReciprocityTheory.ChartRestriction.G.Geo.charOf W : ℕ) : ℤ) ∈ W.comap (C : ℤ →+* MRing (PBlk n)) := by
    rw [hc]
    exact Ideal.mul_mem_right _ _ hg
  exact this

theorem VertPartEq.proof (hCD : ChowDegreeGeoNum.Statement) : VertPartEq.Statement := by
  classical
  intro n e P u hP hu
  have hPp : P.IsPrime := hP.2.1.1
  have hPh : ReciprocityTheory.ChartRestriction.G.Geo.IsHorizontal P := hP.2.2.1
  haveI := hPp
  have hJ : integralModel (genericIdeal P) ⊔ Ideal.span {linForm (fun j => ((u j : ℤ) : 𝓞 ℚ))} =
      (P ⊔ Ideal.span {IndefiniteRowSideFullHecke.ArithBezout.linForm u}).map
        (Ψ n : MRing (PBlk n) →+* MvPolynomial (Fin n) (𝓞 ℚ)) := by
    rw [integralModel_genericIdeal P hPh, Ideal.map_sup, Ideal.map_span, Set.image_singleton,
      RingEquiv.coe_toRingHom, Ψ_linForm]
  have hinj : Function.Injective
      (Ideal.map (Ψ n : MRing (PBlk n) →+* MvPolynomial (Fin n) (𝓞 ℚ))) := by
    intro W₁ W₂ h
    rw [Ideal.map_comap_of_equiv, Ideal.map_comap_of_equiv] at h
    exact Ideal.comap_injective_of_surjective _ (Ψ n).symm.surjective h
  set D := (ReciprocityTheory.ChartRestriction.G.Geo.divSupp_finite P (IndefiniteRowSideFullHecke.ArithBezout.linForm u)).toFinset with hD
  have hDmem : ∀ W, W ∈ D ↔ W ∈ ReciprocityTheory.ChartRestriction.G.Geo.divSupp P (IndefiniteRowSideFullHecke.ArithBezout.linForm u) :=
    fun W => Set.Finite.mem_toFinset _
  have hvert : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ),
      vertComps (genericIdeal P) (fun j => ((u j : ℤ) : 𝓞 ℚ)) v =
        Ideal.map (Ψ n : MRing (PBlk n) →+* MvPolynomial (Fin n) (𝓞 ℚ)) ''
          ↑(D.filter fun W => (W.map (Ψ n : MRing (PBlk n) →+* MvPolynomial (Fin n) (𝓞 ℚ))).comap
            (C : 𝓞 ℚ →+* MvPolynomial (Fin n) (𝓞 ℚ)) = v.asIdeal) := by
    intro v
    ext W'
    simp only [vertComps, relComps, hJ, Set.mem_setOf_eq, minimalPrimes_map_equiv, Set.mem_image,
      Finset.coe_filter, hDmem, ReciprocityTheory.ChartRestriction.G.Geo.divSupp]
    constructor
    · rintro ⟨⟨⟨W, hW, rfl⟩, hrel⟩, hv⟩
      exact ⟨W, ⟨⟨hW, (isRelevant_map_iff W).mp hrel⟩, hv⟩, rfl⟩
    · rintro ⟨W, ⟨⟨hW, hrel⟩, hv⟩, rfl⟩
      exact ⟨⟨⟨W, hW, rfl⟩, (isRelevant_map_iff W).mpr hrel⟩, hv⟩
  let G : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ) → Ideal (MRing (PBlk n)) → ℝ := fun v W =>
    if (W.map (Ψ n : MRing (PBlk n) →+* MvPolynomial (Fin n) (𝓞 ℚ))).comap
        (C : 𝓞 ℚ →+* MvPolynomial (Fin n) (𝓞 ℚ)) = v.asIdeal then
      (localMult ((P ⊔ Ideal.span {IndefiniteRowSideFullHecke.ArithBezout.linForm u}).map
          (Ψ n : MRing (PBlk n) →+* MvPolynomial (Fin n) (𝓞 ℚ)))
          (W.map (Ψ n : MRing (PBlk n) →+* MvPolynomial (Fin n) (𝓞 ℚ))) : ℝ) *
        chowDegree (reduceMod v (W.map (Ψ n : MRing (PBlk n) →+* MvPolynomial (Fin n) (𝓞 ℚ))))
          (e + 1) * Real.log (Ideal.absNorm v.asIdeal)
    else 0
  have hLv : ∀ v, vertTermAt (genericIdeal P) (e + 1) (fun j => ((u j : ℤ) : 𝓞 ℚ)) v =
      ∑ W ∈ D, G v W := by
    intro v
    rw [vertTermAt, hJ, hvert v, finsum_mem_image hinj.injOn, finsum_mem_coe_finset,
      Finset.sum_filter]
  have hfin : ∀ W ∈ D, (Function.support fun v => G v W).Finite := by
    intro W _
    refine Set.Subsingleton.finite (s := {v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ) |
      v.asIdeal = (W.map (Ψ n : MRing (PBlk n) →+* MvPolynomial (Fin n) (𝓞 ℚ))).comap
        (C : 𝓞 ℚ →+* MvPolynomial (Fin n) (𝓞 ℚ))}) ?_ |>.subset ?_
    · intro v₁ h₁ v₂ h₂
      exact IsDedekindDomain.HeightOneSpectrum.ext (h₁.trans h₂.symm)
    · intro v hv
      rw [Function.mem_support] at hv
      by_contra hne
      exact hv (if_neg fun h => hne h.symm)
  have hL : vertTerm (genericIdeal P) (e + 1) (fun j => ((u j : ℤ) : 𝓞 ℚ)) =
      ∑ W ∈ D, ∑ᶠ v, G v W := by
    rw [vertTerm]
    simp_rw [hLv]
    exact finsum_finset_sum_comm D G hfin
  have hR : IndefiniteRowSideFullHecke.ArithBezout.vertPart P e (IndefiniteRowSideFullHecke.ArithBezout.linForm u) =
      ∑ W ∈ D, (ReciprocityTheory.ChartRestriction.G.Geo.multAt (P ⊔ Ideal.span {IndefiniteRowSideFullHecke.ArithBezout.linForm u}) W : ℝ) *
        (if ReciprocityTheory.ChartRestriction.G.Geo.IsHorizontal W then 0 else
          (ReciprocityTheory.ChartRestriction.G.Geo.geoNum e W (fun _ _ => 1) : ℝ) *
            Real.log (ReciprocityTheory.ChartRestriction.G.Geo.charOf W)) := by
    rw [IndefiniteRowSideFullHecke.ArithBezout.vertPart, ← finsum_mem_coe_finset, hD, Set.Finite.coe_toFinset]
  rw [hL, hR]
  refine Finset.sum_congr rfl fun W hW => ?_
  have hWd := (hDmem W).mp hW
  have hsec : ReciprocityTheory.ChartRestriction.G.Geo.IsSectionOn P (ReciprocityTheory.ChartRestriction.G.Geo.fsLine n)
      (IndefiniteRowSideFullHecke.ArithBezout.linForm u) := ⟨fun _ => 1, fun _ => rfl, isMultiHomog_linearForm u, hu⟩
  have hWp : W.IsPrime := hWd.1.1.1
  haveI := hWp
  by_cases hor : ReciprocityTheory.ChartRestriction.G.Geo.IsHorizontal W
  · have h0 := (isHorizontal_iff W).mp hor
    rw [if_pos hor, mul_zero]
    refine finsum_eq_zero_of_forall_eq_zero fun v => if_neg fun h => v.ne_bot ?_
    rw [← h, h0]
  · obtain ⟨hmpp, hcp, hdim⟩ := (ReciprocityTheory.ChartRestriction.G.Geo.divSuppArith Unit (PBlk n) P e
      (ReciprocityTheory.ChartRestriction.G.Geo.fsLine n) (IndefiniteRowSideFullHecke.ArithBezout.linForm u) W hP hsec hWd).2 hor
    rw [Fintype.card_unit] at hdim
    rw [if_neg hor]
    haveI hWΨ : (W.map (Ψ n : MRing (PBlk n) →+* MvPolynomial (Fin n) (𝓞 ℚ))).IsPrime :=
      Ideal.map_isPrime_of_equiv _
    set 𝔭 := (W.map (Ψ n : MRing (PBlk n) →+* MvPolynomial (Fin n) (𝓞 ℚ))).comap
      (C : 𝓞 ℚ →+* MvPolynomial (Fin n) (𝓞 ℚ)) with h𝔭
    have h𝔭ne : 𝔭 ≠ ⊥ := fun h => hor ((isHorizontal_iff W).mpr h)
    let v₀ : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ) := ⟨𝔭, Ideal.comap_isPrime _ _, h𝔭ne⟩
    rw [finsum_eq_single (fun v => G v W) v₀ fun v hv =>
      if_neg fun h => hv (IsDedekindDomain.HeightOneSpectrum.ext h.symm)]
    simp only [G]
    rw [if_pos rfl]
    haveI : v₀.asIdeal.IsMaximal := v₀.isMaximal
    set F := v₀.asIdeal.ResidueField
    have hsurj : Function.Surjective (Int.castRingHom F) := by
      have h1 : Function.Surjective (algebraMap (𝓞 ℚ) F) := by
        rw [IsScalarTower.algebraMap_eq (𝓞 ℚ) (𝓞 ℚ ⧸ v₀.asIdeal) F, RingHom.coe_comp]
        exact (Ideal.bijective_algebraMap_quotient_residueField v₀.asIdeal).2.comp
          Ideal.Quotient.mk_surjective
      intro x
      obtain ⟨y, rfl⟩ := h1 x
      refine ⟨ι.symm y, ?_⟩
      have : (algebraMap (𝓞 ℚ) F).comp (ι : ℤ →+* 𝓞 ℚ) = Int.castRingHom F := RingHom.ext_int _ _
      rw [← this, RingHom.comp_apply, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
    have hp0 : (((ReciprocityTheory.ChartRestriction.G.Geo.charOf W : ℕ) : ℤ) : F) = 0 := by
      have hmem : (ι ((ReciprocityTheory.ChartRestriction.G.Geo.charOf W : ℕ) : ℤ) : 𝓞 ℚ) ∈ v₀.asIdeal := by
        show _ ∈ 𝔭
        rw [h𝔭, Ideal.mem_comap, ← Ψ_C]
        exact Ideal.mem_map_of_mem _ (C_charOf_mem W)
      have : (algebraMap (𝓞 ℚ) F) (ι ((ReciprocityTheory.ChartRestriction.G.Geo.charOf W : ℕ) : ℤ)) = 0 :=
        Ideal.algebraMap_residueField_eq_zero.mpr hmem
      rwa [ι_apply, map_intCast] at this
    have hcd := hCD n e (ReciprocityTheory.ChartRestriction.G.Geo.charOf W) W F hcp hmpp (C_charOf_mem W) hdim hsurj hp0
    have hred : reduceMod v₀ (W.map (Ψ n : MRing (PBlk n) →+* MvPolynomial (Fin n) (𝓞 ℚ))) =
        (IndefiniteRowSideFullHecke.ArithBezout.finIdeal W).map (MvPolynomial.map (Int.castRingHom F)) :=
      reduceMod_map v₀ W
    have hnorm : Ideal.absNorm v₀.asIdeal = ReciprocityTheory.ChartRestriction.G.Geo.charOf W := by
      show Ideal.absNorm 𝔭 = _
      rw [h𝔭, comap_C_map, absNorm_map_comap_C]
    rw [hred, hnorm, localMult_map_eq_multAt]
    have hcdR : ((chowDegree ((IndefiniteRowSideFullHecke.ArithBezout.finIdeal W).map
        (MvPolynomial.map (Int.castRingHom F))) (e + 1) : ℕ) : ℝ) =
        ((ReciprocityTheory.ChartRestriction.G.Geo.geoNum e W (fun _ _ => 1) : ℤ) : ℝ) := by
      rw [← hcd]
      norm_cast
    rw [hcdR]
    ring

end ObjectsChow

end GroundTheory.Heights₂.Heights
