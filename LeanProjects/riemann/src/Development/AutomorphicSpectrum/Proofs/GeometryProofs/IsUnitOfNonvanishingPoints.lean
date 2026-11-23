import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenPtSpecializesOfSpecializes
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueSection
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.UnLocal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolPair
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UnitAtDivOfIsGenAt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
open ReciprocityTheory.ChartRestriction.G.TB.ValAt ReciprocityTheory.ChartRestriction.G.PullbackSections
open GlobalTheory.CompanionTheory.Ar.Flat.GagaC

namespace GlobalTheory.CompanionTheory.Ar.Flat.GagaC

theorem exists_algHom_eq_zero_of_not_isUnit {T : Type} [CommRing T] [Algebra ℂ T] [Algebra.FiniteType ℂ T]
    (a : T) (h : ¬ IsUnit a) : ∃ χ : T →ₐ[ℂ] ℂ, χ a = 0 := by
  obtain ⟨M, hM, haM⟩ := Ideal.exists_le_maximal (Ideal.span {a}) (by rwa [Ne, Ideal.span_singleton_eq_top])
  have hmem : a ∈ M := haM (Ideal.mem_span_singleton_self a)
  letI := Ideal.Quotient.field M
  haveI : Algebra.FiniteType ℂ (T ⧸ M) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ M) (Ideal.Quotient.mkₐ_surjective ℂ M)
  haveI : Module.Finite ℂ (T ⧸ M) := finite_of_finite_type_of_isJacobsonRing ℂ (T ⧸ M)
  have hbij : Function.Bijective (algebraMap ℂ (T ⧸ M)) :=
    ⟨(algebraMap ℂ (T ⧸ M)).injective, IsSepClosed.algebraMap_surjective ℂ (T ⧸ M)⟩
  let e : ℂ ≃ₐ[ℂ] T ⧸ M := AlgEquiv.ofBijective (Algebra.ofId ℂ (T ⧸ M)) hbij
  refine ⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ ℂ M), ?_⟩
  simp [Ideal.Quotient.eq_zero_iff_mem.2 hmem]

theorem fromSpec_comp_structure {X : Scheme.{0}} (s : X ⟶ Sp ℂ) {V : X.Opens} (hV : IsAffineOpen V) :
    hV.fromSpec ≫ s = Spec.map ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ s.appLE ⊤ V (fun _ _ => trivial)) := by
  rw [Spec.map_comp, ← IsAffineOpen.SpecMap_appLE_fromSpec s (isAffineOpen_top _) hV (fun _ _ => trivial)]
  congr 1
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]

private theorem germ_comp_stalkClosedPointTo_eq {X : Scheme.{0}} {V : X.Opens} (hV : IsAffineOpen V)
    (χ : Γ(X, V) ⟶ CommRingCat.of ℂ)
    (hp : (Spec.map χ ≫ hV.fromSpec) (IsLocalRing.closedPoint (CommRingCat.of ℂ)) ∈ V) :
    X.presheaf.germ V _ hp ≫ Scheme.stalkClosedPointTo (Spec.map χ ≫ hV.fromSpec) = χ := by
  rw [Scheme.stalkClosedPointTo_comp]
  erw [Scheme.Hom.germ_stalkMap_assoc]
  rw [IsAffineOpen.fromSpec_app_self, Category.assoc]
  erw [TopCat.Presheaf.germ_res_assoc]
  erw [Scheme.germ_stalkClosedPointTo_Spec]
  simp

theorem isUnit_res_of_forall_point {X : Scheme.{0}} (s : X ⟶ Sp ℂ) [LocallyOfFiniteType s] {U V : X.Opens}
    (hV : IsAffineOpen V) (hVU : V ≤ U) (a : Γ(X, U))
    (h : ∀ x : Sp ℂ ⟶ X, x ≫ s = 𝟙 _ → centre x ∈ U → valAt' x U a ≠ 0) :
    IsUnit (X.presheaf.map (homOfLE hVU).op a) := by
  by_contra hr
  let φ : CommRingCat.of ℂ ⟶ Γ(X, V) :=
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ s.appLE ⊤ V (fun _ _ => trivial)
  letI : Algebra ℂ Γ(X, V) := φ.hom.toAlgebra
  haveI : Algebra.FiniteType ℂ Γ(X, V) := by
    have h1 : (s.appLE ⊤ V (fun _ _ => trivial)).hom.FiniteType :=
      HasRingHomProperty.appLE @LocallyOfFiniteType s inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ _
    have h2 : (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom.FiniteType :=
      RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso _).2
    exact h1.comp h2
  obtain ⟨χ, hχ⟩ := exists_algHom_eq_zero_of_not_isUnit (X.presheaf.map (homOfLE hVU).op a) hr
  let χ' : Γ(X, V) ⟶ CommRingCat.of ℂ := CommRingCat.ofHom χ.toRingHom
  let x : Sp ℂ ⟶ X := Spec.map χ' ≫ hV.fromSpec
  have hxs : x ≫ s = 𝟙 _ := by
    have hc : φ ≫ χ' = 𝟙 _ := by
      ext z
      exact χ.commutes z
    simp only [x, Category.assoc, fromSpec_comp_structure s hV]
    rw [← Spec.map_comp]
    exact (congrArg Spec.map hc).trans (Spec.map_id _)
  have hxV : (Spec.map χ' ≫ hV.fromSpec) (IsLocalRing.closedPoint (CommRingCat.of ℂ)) ∈ V := by
    have hr' : (Spec.map χ' ≫ hV.fromSpec) (IsLocalRing.closedPoint (CommRingCat.of ℂ)) ∈
        Set.range hV.fromSpec := ⟨_, rfl⟩
    rwa [hV.range_fromSpec] at hr'
  have hxU : centre x ∈ U := hVU hxV
  apply h x hxs hxU
  rw [← val_germ x U hxU a]
  have e1 := congrArg (fun f => f.hom (X.presheaf.map (homOfLE hVU).op a)) (germ_comp_stalkClosedPointTo_eq hV χ' hxV)
  have e2 := TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hVU) _ hxV a
  simp only [CommRingCat.comp_apply] at e1
  erw [← e2]
  exact e1.trans hχ

theorem isUnit_of_forall_complexPoint (X : Scheme.{0}) (s : X ⟶ Sp ℂ) (U : X.Opens) (a : Γ(X, U))
    (hs : LocallyOfFiniteType s)
    (h : ∀ x : Sp ℂ ⟶ X, x ≫ s = 𝟙 _ → centre x ∈ U → valAt' x U a ≠ 0) : IsUnit a := by
  refine RingedSpace.isUnit_of_isUnit_germ X.toRingedSpace U a fun p hp => ?_
  obtain ⟨V, hV, hpV, hVU⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hp
  haveI := hs
  have hu := isUnit_res_of_forall_point s hV hVU a h
  have e := TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hVU) p hpV a
  have := hu.map (X.presheaf.germ V p hpV).hom
  rw [e] at this
  exact this

end GlobalTheory.CompanionTheory.Ar.Flat.GagaC
