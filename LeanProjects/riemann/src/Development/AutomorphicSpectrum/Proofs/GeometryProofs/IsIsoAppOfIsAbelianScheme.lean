import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoAppTopOfIsPullbackOfSurjective
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianSchemeSpreadsOutFiniteTypeSubringStatement
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem isAbelianScheme_pullback {S S' : Scheme.{0}} (A : Over S) [GrpObj A]
    (hA : IsAbelianScheme A) (f : S' ⟶ S) : IsAbelianScheme ((Over.pullback f).obj A) :=
  { comm := by have := hA.comm; infer_instance
    smooth := by have := hA.smooth; show Smooth (pullback.snd _ _); infer_instance
    proper := by have := hA.proper; show IsProper (pullback.snd _ _); infer_instance
    geomConnected := by
      have := hA.geomConnected; show GeometricallyConnected (pullback.snd _ _); infer_instance }

theorem isIso_appTop_restrict {S : Scheme.{0}} (A : Over S) [GrpObj A]
    (hA : IsAbelianScheme A) (V : S.Opens) [IsAffine V.toScheme] :
    IsIso (A.hom ∣_ V).appTop := by
  let R : Type := Γ(V.toScheme, ⊤)
  let e : V.toScheme ≅ Sp R := V.toScheme.isoSpec
  let f : Sp R ⟶ S := e.inv ≫ V.ι
  have hf : e.hom ≫ f = V.ι := by simp [f]
  obtain ⟨S₀, B, _, φ, -, hfin, hB, hpb⟩ :=
    GlobalTheory.T.abelianScheme_spreads_out_finiteType_subring R ((Over.pullback f).obj A) ∅ (isAbelianScheme_pullback A hA f)
  have : IsNoetherianRing S₀ := Algebra.FiniteType.isNoetherianRing ℤ S₀
  have := hB.smooth
  have := hB.proper
  have := hB.geomConnected
  have : GeometricallyIntegral B.hom :=
    GlobalTheory.geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres B.hom
  have w : (A.hom ⁻¹ᵁ V).ι ≫ A.hom = (A.hom ∣_ V ≫ e.hom) ≫ f := by
    rw [Category.assoc, hf]
    exact (isPullback_morphismRestrict A.hom V).flip.w
  have sq : IsPullback (pullback.lift _ _ w) (A.hom ∣_ V) (pullback.snd A.hom f) e.hom := by
    refine IsPullback.of_right (h₁₂ := pullback.fst A.hom f) (v₁₃ := A.hom) (h₂₂ := f) ?_
      (pullback.lift_snd _ _ _) (.of_hasPullback _ _)
    rw [pullback.lift_fst, hf]
    exact (isPullback_morphismRestrict A.hom V).flip
  exact GlobalTheory.ProperFunctions.isIso_appTop_baseChange (sq.paste_horiz hpb.1)

theorem isIso_app_of_isAbelianScheme : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A],
    IsAbelianScheme A → ∀ U : S.Opens, IsIso (A.hom.app U) := fun _ A _ hA U ↦
  GlobalTheory.ProperFunctions.isIso_app_of_forall_affineOpens A.hom (fun V ↦
    have : IsAffine V.1.toScheme := V.2
    isIso_appTop_restrict A hA V.1) U

end GlobalTheory.CompanionTheory.Ar.Approx
