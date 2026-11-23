import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjBySmoothIsProperGeometricallyIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoAlgebraisation
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGlueRigidifiedLineBundlesCover
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section

namespace GlobalTheory.FieldBaseChange

theorem inv_left_comp {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) :
    (GrpObj.inv : G' ⟶ G').left ≫ φ = φ ≫ (GrpObj.inv : G ⟶ G).left := by
  have e := congrArg (fun q => q.left) (map_inv (pushHom h G') (𝟙 G'))
  simpa [pushHom, pushPt, Hom.inv_def] using e

theorem abelian_ample_symm_baseChange : ∀ (k Ω : Type) [Field k] [Field Ω] (σ : k →+* Ω) (A₀ : Over (Sp k)) [GrpObj A₀], IsAbelianScheme A₀ → ∀ L : LB A₀.left, L.IsLB → RelAmple A₀ L → LBIso (L.pull (GrpObj.inv : A₀ ⟶ A₀).left) L → IsAbelianScheme ((Over.pullback (spMap σ)).obj A₀) ∧ RelAmple ((Over.pullback (spMap σ)).obj A₀) (L.pull (pullback.fst A₀.hom (spMap σ))) ∧ LBIso ((L.pull (pullback.fst A₀.hom (spMap σ))).pull (GrpObj.inv : (Over.pullback (spMap σ)).obj A₀ ⟶ (Over.pullback (spMap σ)).obj A₀).left) (L.pull (pullback.fst A₀.hom (spMap σ))) := by
  intro k Ω _ _ σ A₀ _ hA L hL hamp hsym
  have h := isGrpPullback_pullback A₀ (spMap σ)
  refine ⟨GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA h, ?_, ?_⟩
  · have := hA.proper
    exact GlobalTheory.AmpleBaseChange.relAmple_of_isPullback hL hamp h.1
  · have hinv := inv_left_comp h
    have i₁ := GlobalTheory.AlgUniq.lbIso_pull_comp hL (pullback.fst A₀.hom (spMap σ))
      (GrpObj.inv : (Over.pullback (spMap σ)).obj A₀ ⟶ (Over.pullback (spMap σ)).obj A₀).left _ rfl
    have i₂ := GlobalTheory.AlgUniq.lbIso_pull_comp hL (GrpObj.inv : A₀ ⟶ A₀).left
      (pullback.fst A₀.hom (spMap σ)) _ hinv.symm
    have i₃ := GlobalTheory.RigidBundleGlue.LBIso.pull hsym (pullback.fst A₀.hom (spMap σ))
    exact (LBIso.trans (pull_isLB (pull_isLB hL _) _) (pull_isLB hL _) (pull_isLB (pull_isLB hL _) _)
      i₁.symm i₂).trans (pull_isLB (pull_isLB hL _) _) (pull_isLB (pull_isLB hL _) _) (pull_isLB hL _) i₃

end GlobalTheory.FieldBaseChange
