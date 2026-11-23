import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndOnId
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical

namespace GlobalTheory.Poinc.Sep.Spz

theorem exists_stalk_factor : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M : RatModel o Ω), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z → ∀ (R : Subalgebra o Ω) (K : Type) [Field K] (x : Sp K ⟶ M.Z) (yK : R →+* K), (∀ a ∈ R, a ∈ M.O (x (closedPoint K))) → (∀ a : R, yK a = M.val x a) → ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsNoetherianRing O) (_ : IsIntegrallyClosed O) (_ : Algebra O Ω) (_ : IsFractionRing O Ω) (xO : Sp O ⟶ M.Z) (u : R →+* O) (v : O →+* K), spMap (algebraMap O Ω) ≫ xO = M.pt ∧ (algebraMap O Ω).comp u = R.val.toRingHom ∧ spMap v ≫ xO = x ∧ v.comp u = yK := by
  intro o Ω _ _ _ _ M hN R K _ x yK hR hy
  haveI := ArithBase.ded (o := o) (Ω := Ω)
  haveI := M.lft
  haveI : IsLocallyNoetherian M.Z := LocallyOfFiniteType.isLocallyNoetherian M.s
  haveI : IsIntegrallyClosed (M.O (x (closedPoint K))) := RatModel.isIntegrallyClosed_O (M := M) hN _
  haveI : IsNoetherianRing (M.O (x (closedPoint K))) :=
    isNoetherianRing_of_ringEquiv _ (M.stalkEquiv (x (closedPoint K)))
  have h1 : CommRingCat.ofHom (M.stalkEquiv (x (closedPoint K))).toRingHom ≫
      CommRingCat.ofHom (algebraMap (M.O (x (closedPoint K))) Ω) =
      M.Z.presheaf.stalkSpecializes (M.pt_specializes (closedPoint Ω) (x (closedPoint K))) ≫
        Scheme.stalkClosedPointTo (R := CommRingCat.of Ω) M.pt := by
    ext a; rfl
  have h3 : CommRingCat.ofHom (M.stalkEquiv (x (closedPoint K))).toRingHom ≫
      CommRingCat.ofHom (RatModel.valLoc x (x (closedPoint K)) specializes_rfl) =
      M.Z.presheaf.stalkSpecializes (specializes_rfl (x := x (closedPoint K))) ≫
        Scheme.stalkClosedPointTo (R := CommRingCat.of K) x := by
    ext a; simp [RatModel.valLoc]
  refine ⟨M.O (x (closedPoint K)), inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, spMap (M.stalkEquiv (x (closedPoint K))).toRingHom ≫ M.Z.fromSpecStalk (x (closedPoint K)),
    (Subalgebra.inclusion (fun a ha => hR a ha) : R →ₐ[o] M.O (x (closedPoint K))).toRingHom,
    RatModel.valLoc x (x (closedPoint K)) specializes_rfl, ?_, ?_, ?_, ?_⟩
  · rw [← Category.assoc, spMap, spMap, ← Spec.map_comp, h1, Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  · ext a; rfl
  · rw [← Category.assoc, spMap, spMap, ← Spec.map_comp, h3, Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  · ext a
    simp [RatModel.valLoc_eq_val, hy]

end GlobalTheory.Poinc.Sep.Spz
