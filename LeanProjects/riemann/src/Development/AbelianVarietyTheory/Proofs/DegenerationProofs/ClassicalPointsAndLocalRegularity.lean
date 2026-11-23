import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemPadicAlgClValuationSubringIffNormLeOne
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RegularOfBoundedAtPadicAlgClPoints
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.JacobsonClosedPointsToolsInt

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH.RatModel

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
open Classical in
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : _root_.GlobalTheory.ZH.RatModel o Ω) in

theorem _root_.GlobalTheory.ZH.RatModel.locallyOfFiniteType_int [Algebra.FiniteType ℤ o] :
    LocallyOfFiniteType (M.s ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap ℤ o)) := by
  haveI := M.lft
  haveI : LocallyOfFiniteType (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap ℤ o)) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.finiteType_algebraMap.mpr inferInstance)
  infer_instance

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
open Classical in
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : _root_.GlobalTheory.ZH.RatModel o Ω) in

theorem _root_.GlobalTheory.ZH.RatModel.flat_int [CharZero Ω] (π : M.Z ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℤ) : Flat π := by
  rw [Flat.iff_flat_stalkMap]
  intro x
  haveI : CharZero (M.Z.presheaf.stalk x) :=
    RingHom.charZero ((M.O x).val.toRingHom.comp
      (M.stalkEquiv x).toRingHom)
  let q : PrimeSpectrum ℤ := π x
  haveI : q.asIdeal.IsPrime := q.isPrime
  letI : Algebra ((Spec.structureSheaf ℤ).presheaf.stalk q) (M.Z.presheaf.stalk x) :=
    (π.stalkMap x).hom.toAlgebra
  have hflat : Module.Flat ℤ (M.Z.presheaf.stalk x) := inferInstance
  have hT : @IsScalarTower ℤ ((Spec.structureSheaf ℤ).presheaf.stalk q)
      (M.Z.presheaf.stalk x)
      (StructureSheaf.stalkAlgebra ℤ q).toSMul this.toSMul (AddCommGroup.toIntModule _).toSMul := by
    refine @IsScalarTower.mk ℤ ((Spec.structureSheaf ℤ).presheaf.stalk q)
      (M.Z.presheaf.stalk x)
      (StructureSheaf.stalkAlgebra ℤ q).toSMul this.toSMul (AddCommGroup.toIntModule _).toSMul
      (fun n s m => ?_)
    have h1 := @Algebra.smul_def' ℤ ((Spec.structureSheaf ℤ).presheaf.stalk q) _ _
      (StructureSheaf.stalkAlgebra ℤ q) n s
    have h2 : @algebraMap ℤ ((Spec.structureSheaf ℤ).presheaf.stalk q) _ _
        (StructureSheaf.stalkAlgebra ℤ q) n = n :=
      eq_intCast _ n
    rw [h2] at h1
    erw [h1]
    rw [mul_smul, Int.cast_smul_eq_zsmul]
  exact (@Module.flat_iff_of_isLocalization ℤ ((Spec.structureSheaf ℤ).presheaf.stalk q) _ _
    (StructureSheaf.stalkAlgebra ℤ q) q.asIdeal.primeCompl (StructureSheaf.IsLocalization.to_stalk ℤ q)
    (M.Z.presheaf.stalk x) _ _ _ hT).mpr hflat

end GlobalTheory.ZH.RatModel

namespace GlobalTheory.ZH

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
open Classical in

theorem _root_.GlobalTheory.ZH.classical_points_and_local_regularity :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [Algebra.FiniteType ℤ o] [CharZero Ω]
      (M : _root_.GlobalTheory.ZH.RatModel o Ω)
      (U₀ : M.Z.Opens), _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z →
      ((∀ U₁ : M.Z.Opens, U₁ ≤ U₀ → (U₁ : Set M.Z).Nonempty →
        ∀ z : M.Z, IsClosed ({z} : Set M.Z) →
        (∃ (p : ℕ) (_ : Fact p.Prime)
          (y : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (_root_.GlobalTheory.ZH.OO p) ⟶ M.Z),
          M.Cen U₁ z y) ∧
        ∀ φ ∈ M.ringOn U₁,
          (∀ (p : ℕ) [Fact p.Prime]
            (y : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (_root_.GlobalTheory.ZH.OO p) ⟶ M.Z),
            M.Cen U₁ z y →
            ‖M.val (_root_.GlobalTheory.ZH.gPt p ≫ y) φ‖ ≤ 1) →
          φ ∈ M.O z) ∧ JacobsonSpace M.Z) := by
  intro o Ω _ _ _ _ _ M U₀ hN
  haveI := _root_.GlobalTheory.ZH.RatModel.locallyOfFiniteType_int M
  haveI : Flat (M.s ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap ℤ o)) := M.flat_int _
  refine ⟨fun U₁ _ hU₁ z hz => ⟨?_, ?_⟩,
    _root_.GlobalTheory.jacobsonSpace_of_locallyOfFiniteType_int (M.s ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap ℤ o))⟩
  · obtain ⟨p, hp, y, h1, h2⟩ := _root_.GlobalTheory.padicAlgCl_integral_points.1 M.Z
      (M.s ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap ℤ o)) z hz U₁ hU₁
    exact ⟨p, hp, y, h1, h2⟩
  · intro φ hφ hb
    obtain ⟨f, rfl⟩ :=
      (_root_.GlobalTheory.ZH.RatModel.mem_ringOn_iff_exists hU₁).1 hφ
    haveI := _root_.GlobalTheory.ZH.RatModel.isIntegrallyClosed_O hN z
    haveI : IsIntegrallyClosed (M.Z.presheaf.stalk z) :=
      IsIntegrallyClosed.of_equiv (M.stalkEquiv z).symm
    obtain ⟨W, ψ, hzW, h⟩ := _root_.GlobalTheory.regular_of_bounded_at_padicAlgCl_points.1 M.Z
      (M.s ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap ℤ o)) z hz inferInstance U₁ f hU₁
      (fun p _ y hy hr => by
        have hle := hb p y ⟨hy, hr⟩
        rwa [_root_.GlobalTheory.ZH.RatModel.val_valF hr] at hle)
    rw [_root_.GlobalTheory.ZH.RatModel.mem_O]
    refine ⟨W, ψ, hzW, ?_⟩
    have hne := M.nonempty_inf ⟨z, hzW⟩ hU₁
    have hv := congrArg (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valF M.pt _) h
    rwa [M.valF_resG _ hne,
      M.valF_resG _ hne] at hv

end GlobalTheory.ZH
