import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIntegrallyClosedInFractionFieldPowerSeries

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
private lemma exists_retraction_of_flat_quasiFinite (V K : Type) [CommRing V] [IsDomain V]
    [ValuationRing V] [Field K] [IsAlgClosed K] [Algebra V K] [IsFractionRing V K] {B : Type}
    [CommRing B] (φ : V →+* B) (hflat : φ.Flat) (hqf : φ.QuasiFinite) (q : Ideal B) [q.IsPrime]
    (hq : q.comap φ = IsLocalRing.maximalIdeal V) :
    ∃ ψ : B →+* V, ψ.comp φ = RingHom.id V ∧ (IsLocalRing.maximalIdeal V).comap ψ = q := by
  letI : Algebra V B := φ.toAlgebra
  haveI : Module.Flat V B := hflat
  haveI : Algebra.QuasiFinite V B := hqf.toAlgebra
  haveI : q.LiesOver (IsLocalRing.maximalIdeal V) := ⟨hq.symm⟩
  obtain ⟨P, hPq, hP, hPl⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := (⊥ : Ideal V))
    (q := IsLocalRing.maximalIdeal V) q bot_le
  have hPV : P.comap φ = ⊥ := hPl.over.symm
  set κ := P.ResidueField
  have hinj : Function.Injective (algebraMap V κ) := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    rw [IsScalarTower.algebraMap_apply V B κ, Ideal.algebraMap_residueField_eq_zero] at hv
    have : v ∈ P.comap φ := hv
    rwa [hPV, Ideal.mem_bot] at this
  letI : Algebra K κ := (IsFractionRing.lift (K := K) hinj).toAlgebra
  haveI : IsScalarTower V K κ := IsScalarTower.of_algebraMap_eq
    (fun v => (IsFractionRing.lift_algebraMap (K := K) hinj v).symm)
  haveI : Algebra.QuasiFinite K κ := Algebra.QuasiFinite.of_restrictScalars V K κ
  haveI : Module.Finite K κ := Module.Finite.of_quasiFinite
  let e : K ≃+* κ := RingEquiv.ofBijective (algebraMap K κ)
    ⟨(algebraMap K κ).injective, IsSepClosed.algebraMap_surjective K κ⟩
  let χ : B →+* K := e.symm.toRingHom.comp (algebraMap B κ)
  have hχφ : ∀ v, χ (φ v) = algebraMap V K v := by
    intro v
    apply e.injective
    simp only [χ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.apply_symm_apply]
    change algebraMap B κ (algebraMap V B v) = algebraMap K κ (algebraMap V K v)
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have hχ0 : ∀ b, χ b = 0 → b ∈ q := by
    intro b hb
    apply hPq
    rw [← Ideal.algebraMap_residueField_eq_zero]
    have : e (χ b) = algebraMap B κ b := by simp [χ]
    rw [← this, hb, map_zero]
  have hφq : ∀ v ∈ IsLocalRing.maximalIdeal V, φ v ∈ q := by
    intro v hv
    rw [← hq] at hv
    exact hv
  have hmem : ∀ b, χ b ∈ (algebraMap V K).range := by
    intro b
    rcases ValuationRing.isInteger_or_isInteger V (χ b) with ⟨v, hv⟩ | ⟨v, hv⟩
    · exact ⟨v, hv⟩
    by_cases hb0 : χ b = 0
    · exact ⟨0, by rw [hb0, map_zero]⟩
    by_cases hvu : IsUnit v
    · obtain ⟨u, rfl⟩ := hvu
      refine ⟨↑u⁻¹, ?_⟩
      rw [← inv_inv (χ b), ← hv]
      exact map_units_inv (algebraMap V K : V →* K) u
    · exfalso
      have hvm : v ∈ IsLocalRing.maximalIdeal V := hvu
      have h1 : χ (b * φ v - 1) = 0 := by
        rw [map_sub, map_mul, map_one, hχφ, hv, mul_inv_cancel₀ hb0, sub_self]
      have h2 := hχ0 _ h1
      have h3 : b * φ v ∈ q := q.mul_mem_left b (hφq v hvm)
      have h4 := q.sub_mem h3 h2
      rw [sub_sub_cancel] at h4
      exact ‹q.IsPrime›.ne_top ((Ideal.eq_top_iff_one q).mpr h4)
  let j := algebraMap V K
  have hj : Function.Injective j := IsFractionRing.injective V K
  let e₂ : V ≃+* j.range := RingEquiv.ofBijective j.rangeRestrict
    ⟨fun a b h => hj (congrArg Subtype.val h), j.rangeRestrict_surjective⟩
  let ψ : B →+* V := e₂.symm.toRingHom.comp (χ.codRestrict j.range hmem)
  have hψ : ∀ b, j (ψ b) = χ b := by
    intro b
    have : e₂ (ψ b) = χ.codRestrict j.range hmem b := by simp [ψ]
    exact congrArg Subtype.val this
  refine ⟨ψ, ?_, ?_⟩
  · ext v
    apply hj
    simp only [RingHom.comp_apply, RingHom.id_apply]
    rw [hψ, hχφ]
  · ext b
    rw [Ideal.mem_comap]
    constructor
    · intro hb
      have h1 : χ (b - φ (ψ b)) = 0 := by rw [map_sub, hχφ, hψ, sub_self]
      have h2 := hχ0 _ h1
      have h3 := hφq _ hb
      simpa using q.add_mem h2 h3
    · intro hb
      by_contra hn
      have hu : IsUnit (ψ b) := by
        by_contra h
        exact hn h
      obtain ⟨u, hu⟩ := hu
      have h1 : χ (b * φ ↑u⁻¹ - 1) = 0 := by
        rw [map_sub, map_mul, map_one, hχφ, ← hψ, ← hu, ← map_mul, Units.mul_inv, map_one, sub_self]
      have h2 := hχ0 _ h1
      have h3 : b * φ ↑u⁻¹ ∈ q := q.mul_mem_right _ hb
      have h4 := q.sub_mem h3 h2
      rw [sub_sub_cancel] at h4
      exact ‹q.IsPrime›.ne_top ((Ideal.eq_top_iff_one q).mpr h4)

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
private lemma exists_section_through_closed_fiber_point (V K : Type) [CommRing V] [IsDomain V]
    [ValuationRing V] [Field K] [IsAlgClosed K] [Algebra V K] [IsFractionRing V K]
    (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of V)) [LocallyQuasiFinite f] [Flat f] (x : X)
    (hx : f x = IsLocalRing.closedPoint V) :
    ∃ s : Spec (CommRingCat.of V) ⟶ X, s ≫ f = 𝟙 _ ∧ s (IsLocalRing.closedPoint V) = x := by
  obtain ⟨_, ⟨U, hU₀, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hU : IsAffineOpen U := hU₀
  have hg : Spec.map (Spec.preimage (hU.fromSpec ≫ f)) = hU.fromSpec ≫ f := Spec.map_preimage _
  set φ := Spec.preimage (hU.fromSpec ≫ f)
  haveI : Flat hU.fromSpec := inferInstance
  haveI : LocallyQuasiFinite hU.fromSpec := inferInstance
  haveI : Flat (hU.fromSpec ≫ f) := MorphismProperty.comp_mem _ _ _ ‹_› ‹_›
  haveI : LocallyQuasiFinite (hU.fromSpec ≫ f) := MorphismProperty.comp_mem _ _ _ ‹_› ‹_›
  have hflat : φ.hom.Flat := (HasRingHomProperty.Spec_iff (P := @Flat)).mp (hg ▸ inferInstance)
  have hqf : φ.hom.QuasiFinite :=
    (HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite)).mp (hg ▸ inferInstance)
  have hqx : hU.fromSpec (hU.primeIdealOf ⟨x, hxU⟩) = x := hU.fromSpec_primeIdealOf _
  set q := hU.primeIdealOf ⟨x, hxU⟩
  have hq : q.asIdeal.comap φ.hom = IsLocalRing.maximalIdeal V := by
    have h1 : (Spec.map φ) q = IsLocalRing.closedPoint V := by
      rw [hg]
      exact (congrArg f hqx).trans hx
    exact congrArg PrimeSpectrum.asIdeal h1
  obtain ⟨ψ, hψ, hψq⟩ := exists_retraction_of_flat_quasiFinite V K φ.hom hflat hqf q.asIdeal hq
  refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ hU.fromSpec, ?_, ?_⟩
  · rw [Category.assoc, ← hg, ← Spec.map_comp]
    have : φ ≫ CommRingCat.ofHom ψ = 𝟙 _ := by ext1; exact hψ
    rw [this, Spec.map_id]
  · have : (Spec.map (CommRingCat.ofHom ψ)) (IsLocalRing.closedPoint V) = q :=
      PrimeSpectrum.ext hψq
    exact (congrArg hU.fromSpec this).trans hqx

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in

theorem _root_.GlobalTheory.exists_section_of_quasiFinite_flat :
    ∀ (V K : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [IsAlgClosed K]
      [Algebra V K] [IsFractionRing V K] (X : Scheme.{0}) (f : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp V) [IsSeparated f]
      [QuasiCompact f] [LocallyOfFiniteType f] [LocallyQuasiFinite f] [Flat f] (x : X),
      f x = IsLocalRing.closedPoint V →
        ∃ s : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp V ⟶ X, s ≫ f = 𝟙 _ ∧ s (IsLocalRing.closedPoint V) = x := by
  intro V K _ _ _ _ _ _ _ X f _ _ _ _ _ x hx
  exact exists_section_through_closed_fiber_point V K X f x hx

end GlobalTheory
