import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.GenericFlat

open AlgebraicGeometry CategoryTheory Limits in

theorem _root_.GlobalTheory.GenericFlat.injective_of_apply_eq_genericPoint {O K : Type} [CommRing O] [IsDomain O] [Field K]
    (δ : O →+* K) (pt : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K) (h : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap δ pt = genericPoint (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp O)) :
    Function.Injective δ := by
  change (Spec.map (CommRingCat.ofHom δ)) pt = genericPoint (Spec (CommRingCat.of O)) at h
  rw [genericPoint_eq_bot_of_affine] at h
  have hpt : pt.asIdeal = ⊥ := Ideal.eq_bot_of_prime (h := pt.isPrime) _
  have h2 := congrArg PrimeSpectrum.asIdeal h
  change Ideal.comap δ pt.asIdeal = ⊥ at h2
  rw [hpt, ← RingHom.ker_eq_comap_bot] at h2
  exact (RingHom.injective_iff_ker_eq_bot δ).mpr h2

theorem exists_charZero_specializes (O : Type) [CommRing O] [IsDomain O] [CharZero O] (T : Scheme.{0})
    (s : T ⟶ Sp O) [Flat s] (x : T) : ∃ ξ : T, ξ ⤳ x ∧ CharZero (T.residueField ξ) := by
  obtain ⟨ξ, hξ, e⟩ := Flat.generalizingMap s (genericPoint_specializes (s x))
  refine ⟨ξ, hξ, ?_⟩
  obtain ⟨δ, hδ⟩ := Spec.map_surjective (T.fromSpecResidueField ξ ≫ s)
  have hi : Function.Injective δ.hom := by
    refine injective_of_apply_eq_genericPoint (K := T.residueField ξ) δ.hom
      (⊥ : PrimeSpectrum (T.residueField ξ)) ?_
    change Spec.map δ _ = _
    rw [hδ]
    exact (Scheme.Hom.comp_apply _ _ _).trans
      ((congrArg s (Scheme.fromSpecResidueField_apply ξ _)).trans e)
  exact charZero_of_injective_ringHom hi

open AlgebraicGeometry CategoryTheory Limits in

theorem _root_.GlobalTheory.GenericFlat.apply_eq_genericPoint {O : Type} [CommRing O] [IsDomain O]
    {T : Scheme.{0}} (s : T ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp O) [Flat s]
    {t : T} (ht : t ∈ genericPoints T) : s t = genericPoint (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp O) := by
  obtain ⟨t', hspec, heq⟩ := Flat.generalizingMap s
    ((genericPoint_spec (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp O)).specializes (Set.mem_univ (s t)))
  have hsub : closure {t} ⊆ closure {t'} := specializes_iff_closure_subset.mp hspec
  have hcl : closure {t} = closure {t'} :=
    (show closure {t} ∈ irreducibleComponents T from ht).eq_of_le
      isIrreducible_singleton.closure hsub
  have hback : t ⤳ t' := specializes_iff_closure_subset.mpr hcl.ge
  rw [← heq, (hspec.antisymm hback).eq]

open AlgebraicGeometry CategoryTheory Limits in

theorem _root_.GlobalTheory.GenericFlat.generic_charZero_and_flat : (∀ (O : Type) [CommRing O] [IsDomain O] [CharZero O] (T : Scheme.{0}) (s : T ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp O), Flat s → ∀ x : T, ∃ ξ : T, ξ ⤳ x ∧ CharZero (T.residueField ξ)) ∧ ∀ (R O : Type) [CommRing R] [IsDedekindDomain R] [CommRing O] [IsDomain O] (b : R →+* O) (T : Scheme.{0}) (s : T ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp O) (V K : Type) [CommRing V] [IsDomain V] [Field K] [Algebra V K] [IsFractionRing V K] (x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K ⟶ T) (v : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp V ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp O), Function.Injective b → Flat s → Set.range x ⊆ genericPoints T → x ≫ s = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap V K) ≫ v → Flat (v ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap b) := by
  refine ⟨fun O _ _ _ T s hs x => ?_,
    fun R O _ _ _ _ b T s V K _ _ _ _ _ x v hb hs hx hxs => ?_⟩
  · obtain ⟨ξ, hξ⟩ := QuasiSober.sober (isIrreducible_irreducibleComponent (x := x))
      (isClosed_of_mem_irreducibleComponents _ (irreducibleComponent_mem_irreducibleComponents x))
    refine ⟨ξ, hξ.specializes mem_irreducibleComponent, ?_⟩
    have hgen : ξ ∈ genericPoints T := by
      change closure {ξ} ∈ irreducibleComponents T
      rw [hξ.def]
      exact irreducibleComponent_mem_irreducibleComponents x
    let δ : O →+* T.residueField ξ := (Spec.preimage (T.fromSpecResidueField ξ ≫ s)).hom
    have hδ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap δ = T.fromSpecResidueField ξ ≫ s := Spec.map_preimage _
    have hinj : Function.Injective δ := by
      refine _root_.GlobalTheory.GenericFlat.injective_of_apply_eq_genericPoint δ
        (IsLocalRing.closedPoint (T.residueField ξ)) ?_
      rw [hδ]
      exact (congrArg s (Scheme.fromSpecResidueField_apply ξ _)).trans
        (_root_.GlobalTheory.GenericFlat.apply_eq_genericPoint s hgen)
    exact charZero_of_injective_ringHom hinj
  · let φ : O →+* V := (Spec.preimage v).hom
    have hv : v = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap φ := (Spec.map_preimage v).symm
    have hcomp : x ≫ s = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap ((algebraMap V K).comp φ) := by
      rw [hxs, hv]; exact (Spec.map_comp _ _).symm
    let pt : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K := IsLocalRing.closedPoint K
    have hpt : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap ((algebraMap V K).comp φ) pt = genericPoint (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp O) := by
      rw [← hcomp, Scheme.Hom.comp_apply]
      exact _root_.GlobalTheory.GenericFlat.apply_eq_genericPoint s (hx ⟨pt, rfl⟩)
    have hφ : Function.Injective φ := by
      have h := _root_.GlobalTheory.GenericFlat.injective_of_apply_eq_genericPoint _ pt hpt
      rw [RingHom.coe_comp] at h
      exact h.of_comp
    have hψ : Function.Injective (φ.comp b) := hφ.comp hb
    have hmap : v ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap b = Spec.map (CommRingCat.ofHom (φ.comp b)) := by
      rw [hv]; exact (Spec.map_comp _ _).symm
    rw [hmap, HasRingHomProperty.Spec_iff (P := @Flat)]
    letI := (φ.comp b).toAlgebra
    change Module.Flat R V
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, Submodule.eq_bot_iff]
    intro m hm
    obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff m).mp hm
    rw [Submonoid.smul_def, Algebra.smul_def, RingHom.algebraMap_toAlgebra] at ha
    have h0 : (φ.comp b) a ≠ 0 := fun h =>
      nonZeroDivisors.coe_ne_zero a (hψ (h.trans (map_zero _).symm))
    exact (mul_eq_zero.mp ha).resolve_left h0

end GlobalTheory.GenericFlat
