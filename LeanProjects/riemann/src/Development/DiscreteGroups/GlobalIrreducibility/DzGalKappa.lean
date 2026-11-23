import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import ReciprocityTheory.GaloisValuations.GlobalB
import Development.DiscreteGroups.GlobalIrreducibility.DzApprox
import Development.DiscreteGroups.GlobalIrreducibility.ExistsOfMemKOne
import Development.DiscreteGroups.GlobalIrreducibility.ExistsUniformizerValuation

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal ValuativeRel GlobalTheory.SplitWeil

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option linter.style.haveILetI false in
theorem kappa_range_sub {K F : Type} [Field K] [Field F] [DecidableEq F] [Finite K] (f : K →+* F) :
    Set.range f ⊆ ↑((Polynomial.X ^ Nat.card K - Polynomial.X : Polynomial F).roots.toFinset) := by
  letI := Fintype.ofFinite K
  have hq1 : 1 < Nat.card K := Finite.one_lt_card
  rintro _ ⟨z, rfl⟩
  rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots (FiniteField.X_pow_card_sub_X_ne_zero F hq1),
    Polynomial.IsRoot.def]
  have hz : z ^ Nat.card K = z := by rw [Nat.card_eq_fintype_card]; exact FiniteField.pow_card z
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
  rw [← map_pow, hz, sub_self]

theorem kappa_exists {K1 K2 F : Type} [Field K1] [Field K2] [Field F] [Finite K1] [Finite K2]
    (hc : Nat.card K1 = Nat.card K2) (f1 : K1 →+* F) (f2 : K2 →+* F) :
    ∃ κ : K1 ≃+* K2, ∀ z, f2 (κ z) = f1 z := by
  classical
  have hq1 : 1 < Nat.card K1 := Finite.one_lt_card
  have hRc : (Polynomial.X ^ Nat.card K1 - Polynomial.X : Polynomial F).roots.toFinset.card ≤ Nat.card K1 :=
    (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' _).trans
      (FiniteField.X_pow_card_sub_X_natDegree_eq F hq1).le)
  have hr : ∀ (K : Type) [Field K] [Finite K], Nat.card K = Nat.card K1 → ∀ f : K →+* F,
      Set.range f = ↑((Polynomial.X ^ Nat.card K1 - Polynomial.X : Polynomial F).roots.toFinset) := by
    intro K _ _ hK f
    have hs := kappa_range_sub f
    rw [hK] at hs
    refine Set.eq_of_subset_of_ncard_le hs ?_ (Finset.finite_toSet _)
    rw [Set.ncard_coe_finset, ← Set.image_univ, Set.ncard_image_of_injective _ f.injective, Set.ncard_univ, hK]
    exact hRc
  have heq : f1.range = f2.range := SetLike.coe_injective (by
    rw [RingHom.coe_range, RingHom.coe_range, hr K1 rfl f1, hr K2 hc.symm f2])
  let e1 : K1 ≃+* f1.range := RingEquiv.ofBijective f1.rangeRestrict
    ⟨fun a b h => f1.injective (congrArg Subtype.val h), f1.rangeRestrict_surjective⟩
  let e2 : K2 ≃+* f2.range := RingEquiv.ofBijective f2.rangeRestrict
    ⟨fun a b h => f2.injective (congrArg Subtype.val h), f2.rangeRestrict_surjective⟩
  refine ⟨(e1.trans (RingEquiv.subringCongr heq)).trans e2.symm, fun z => ?_⟩
  exact congrArg Subtype.val (e2.apply_symm_apply ((RingEquiv.subringCongr heq) (e1 z)))

section Ring

variable {Ω : Type} [Field Ω]

def kappaToA {F : Type} [Field F] [NumberField F] [Algebra F Ω] (A : ValuationSubring Ω) : 𝓞 F →+* A :=
  ((algebraMap F Ω).comp (algebraMap (𝓞 F) F)).codRestrict A fun x =>
    mem_of_isIntegral_int A (NumberField.RingOfIntegers.isIntegral_coe x).algebraMap

def kappaQ {F : Type} [Field F] [NumberField F] [Algebra F Ω] (A : ValuationSubring Ω) :
    𝓞 F →+* IsLocalRing.ResidueField A :=
  (IsLocalRing.residue A).comp (kappaToA A)

theorem kappa_ker_A {F : Type} [Field F] [NumberField F] [Algebra F Ω] (A : ValuationSubring Ω)
    (v : HeightOneSpectrum (𝓞 F)) (hv : IsPlaceOver A v) :
    RingHom.ker (kappaQ A : 𝓞 F →+* IsLocalRing.ResidueField A) = v.asIdeal := by
  ext y
  rw [RingHom.mem_ker, kappaQ, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff,
    ValuationSubring.valuation_lt_one_iff, ← hv y]
  rfl

end Ring

section Compl

variable {L : Type} [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L))

theorem kappa_val_le_iff (y : v.adicCompletion L) :
    valuation (v.adicCompletion L) y ≤ 1 ↔ Valued.v y ≤ 1 :=
  (DiscreteGroups.sglob.DzIso.val_le_iff y).trans Valued.toNormedField.norm_le_one_iff

theorem kappa_val_lt_iff (y : v.adicCompletion L) :
    valuation (v.adicCompletion L) y < 1 ↔ Valued.v y < 1 :=
  (DiscreteGroups.sglob.DzIso.val_lt_iff y).trans Valued.toNormedField.norm_lt_one_iff

theorem kappa_v_int (y : 𝓞 L) :
    Valued.v (algebraMap L (v.adicCompletion L) (y : L)) = v.valuation L (y : L) :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 L) v (y : L)

def kappaToO : 𝓞 L →+* 𝒪[v.adicCompletion L] :=
  ((algebraMap L (v.adicCompletion L)).comp (algebraMap (𝓞 L) L)).codRestrict 𝒪[v.adicCompletion L] fun y =>
    (Valuation.mem_integer_iff _ _).2 ((kappa_val_le_iff v _).2
      ((kappa_v_int v y).trans_le (v.valuation_le_one y)))

def kappaP : 𝓞 L →+* 𝓀[v.adicCompletion L] := (IsLocalRing.residue 𝒪[v.adicCompletion L]).comp (kappaToO v)

theorem kappa_ker_O : RingHom.ker (kappaP v) = v.asIdeal := by
  ext y
  rw [RingHom.mem_ker, kappaP, RingHom.comp_apply, ← map_zero (IsLocalRing.residue 𝒪[v.adicCompletion L]),
    residue_eq_iff_valuation_lt]
  have e1 : ((kappaToO v y : 𝒪[v.adicCompletion L]) : v.adicCompletion L) -
      ((0 : 𝒪[v.adicCompletion L]) : v.adicCompletion L) = algebraMap L (v.adicCompletion L) (y : L) := by
    rw [ZeroMemClass.coe_zero, sub_zero]
    rfl
  rw [e1, kappa_val_lt_iff v, kappa_v_int v y]
  exact HeightOneSpectrum.valuation_lt_one_iff_mem v y

theorem kappa_surj_O : Function.Surjective (kappaP v) := by
  intro z
  obtain ⟨u, rfl⟩ := IsLocalRing.residue_surjective z
  have hu : Valued.v (u : v.adicCompletion L) ≤ 1 :=
    (kappa_val_le_iff v _).1 ((Valuation.mem_integer_iff _ _).1 u.2)
  obtain ⟨x, hx⟩ := exists_int_approx_compl v (u : v.adicCompletion L) hu
  refine ⟨x, ?_⟩
  rw [kappaP, RingHom.comp_apply, residue_eq_iff_valuation_lt, Valuation.map_sub_swap]
  exact (kappa_val_lt_iff v _).2 hx

end Compl

theorem exists_resIso {L E' Ω : Type} [Field L] [NumberField L] [Field E'] [NumberField E'] [Field Ω]
    [Algebra L Ω] [Algebra E' Ω] [IsAlgClosure L Ω] [IsAlgClosure E' Ω] (g : ℕ) [Fact g.Prime] (n : ℕ)
    (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 L)) (hv : IsPlaceOver A v) (w' : HeightOneSpectrum (𝓞 E'))
    (h' : IsPlaceOver A w') (hvN : normV v = g ^ n) (hwN : normV w' = g ^ n) (K : Type) [Field K]
    (red : 𝓞 E' →+* K) (hr : Function.Surjective red) (hk : RingHom.ker red = w'.asIdeal) :
    ∃ κ : 𝓀[v.adicCompletion L] ≃+* K, ∀ (u : 𝒪[v.adicCompletion L]) (y : 𝓞 L) (x : 𝓞 E'),
      Valued.v ((u : v.adicCompletion L) - algebraMap L (v.adicCompletion L) (y : L)) < 1 →
      A.valuation (algebraMap L Ω (y : L) - algebraMap E' Ω (x : E')) < 1 →
      κ (IsLocalRing.residue 𝒪[v.adicCompletion L] u) = red x := by
  classical
  have hkp : RingHom.ker (kappaP v) = RingHom.ker (kappaQ A : 𝓞 L →+* IsLocalRing.ResidueField A) := by
    rw [kappa_ker_O, kappa_ker_A A v hv]
  have hkr : RingHom.ker red = RingHom.ker (kappaQ A : 𝓞 E' →+* IsLocalRing.ResidueField A) := by
    rw [hk, kappa_ker_A A w' h']
  let e1 := RingHom.quotientKerEquivOfSurjective (kappa_surj_O v)
  let e2 := RingHom.quotientKerEquivOfSurjective hr
  let f1 : 𝓀[v.adicCompletion L] →+* IsLocalRing.ResidueField A :=
    (Ideal.Quotient.lift (RingHom.ker (kappaP v)) (kappaQ A)
      fun a ha => (RingHom.mem_ker).1 (hkp ▸ ha)).comp e1.symm.toRingHom
  let f2 : K →+* IsLocalRing.ResidueField A :=
    (Ideal.Quotient.lift (RingHom.ker red) (kappaQ A)
      fun a ha => (RingHom.mem_ker).1 (hkr ▸ ha)).comp e2.symm.toRingHom
  have hf1 : ∀ y, f1 (kappaP v y) = kappaQ A y := fun y => by
    have : e1.symm (kappaP v y) = Ideal.Quotient.mk _ y := e1.symm_apply_eq.2 rfl
    simp only [f1, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, this,
      Ideal.Quotient.lift_mk]
  have hf2 : ∀ x, f2 (red x) = kappaQ A x := fun x => by
    have : e2.symm (red x) = Ideal.Quotient.mk _ x := e2.symm_apply_eq.2 rfl
    simp only [f2, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, this,
      Ideal.Quotient.lift_mk]
  have hgn : g ^ n ≠ 0 := pow_ne_zero _ (Fact.out : g.Prime).ne_zero
  have hc1 : Nat.card 𝓀[v.adicCompletion L] = g ^ n := by
    rw [← hvN, ← GlobalTheory.LocLanglands.resCard_eq_normV v]
    rfl
  have hc2 : Nat.card K = g ^ n := by
    rw [← hwN, normV]
    exact (Nat.card_congr ((Ideal.quotEquivOfEq hk.symm).trans e2).toEquiv).symm
  have : Finite 𝓀[v.adicCompletion L] := Nat.finite_of_card_ne_zero (by rw [hc1]; exact hgn)
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hc2]; exact hgn)
  obtain ⟨κ, hκ⟩ := kappa_exists (hc1.trans hc2.symm) f1 f2
  refine ⟨κ, fun u y x huy hyx => f2.injective ?_⟩
  rw [hκ, hf2]
  have h1 : IsLocalRing.residue 𝒪[v.adicCompletion L] u = kappaP v y := by
    rw [kappaP, RingHom.comp_apply, residue_eq_iff_valuation_lt]
    exact (kappa_val_lt_iff v _).2 huy
  rw [h1, hf1, kappaQ, kappaQ, RingHom.comp_apply, RingHom.comp_apply, ← sub_eq_zero, ← map_sub,
    IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
  exact hyx

end DiscreteGroups.sglob.DzType
