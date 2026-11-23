import Mathlib
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.OpensRangeChartYSupOpensRangeChartZ
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.ExistsUniqueEqConstMulOriginSec
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsStandardSmoothOfRelativeDimensionAwayJacobian
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddXYZOrChordXYZOrOriginXYZNeZero
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCommGrpObjWeierstrassSchemeStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeSchemeOver
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveFst
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.OriginLineBundlePolarisationStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.WeierstrassCurve GlobalTheory.AddLaw

namespace GlobalTheory.WeierstrassCurve

theorem polarised_of_grpObj (R : Type) [CommRing R] (W : _root_.WeierstrassCurve R)
    (hΔ : IsUnit W.Δ) [GrpObj (schemeOver W)] (hc : IsCommMonObj (schemeOver W))
    (hη : η[schemeOver W].left = zero W) :
    IsAbelianScheme (schemeOver W) ∧ SmoothOfRelativeDimension 1 (schemeOver W).hom ∧
      (originLB W).IsLB ∧ Out.Rigidified (schemeOver W) (originLB W) ∧
      Out.Sym (schemeOver W) (originLB W) ∧ Out.RelAmple (schemeOver W) (originLB W) ∧
      Out.KTriv (schemeOver W) (originLB W) := by
  obtain ⟨hrig, hsym, hamp, hk⟩ := GlobalTheory.T.originLineBundle_polarisation R W hc hη
  exact ⟨isAbelianScheme_schemeOver R W hΔ hc, smoothOfRelativeDimension_toSpec_of_isUnit W hΔ,
    originLB_isLB W, hrig, hsym, hamp, hk⟩

theorem exists_grpObj_polarised (R : Type) [CommRing R] (W : _root_.WeierstrassCurve R)
    (hΔ : IsUnit W.Δ) :
    ∃ _ : GrpObj (schemeOver W), IsCommMonObj (schemeOver W) ∧ η[schemeOver W].left = zero W ∧
      (∀ (A : Type) [CommRing A] (ρ : R →+* A) (P Q T : Fin 3 → A)
        (hP : IsUnimodularSol (W.map ρ) P) (hQ : IsUnimodularSol (W.map ρ) Q)
        (hT : IsUnimodularSol (W.map ρ) T),
        (Proportional T ((W.map ρ).toProjective.addXYZ P Q) ∧
          Proportional T (diagXYZ (W.map ρ).toProjective P Q)) →
        ∀ x y : Over.mk (spMap ρ) ⟶ schemeOver W, x.left = ptHom W ρ P hP →
          y.left = ptHom W ρ Q hQ → (lift x y ≫ μ[schemeOver W]).left = ptHom W ρ T hT) ∧
      (∀ (A : Type) [CommRing A] (ρ : R →+* A) (P : Fin 3 → A)
        (hP : IsUnimodularSol (W.map ρ) P),
        ∃ hN : IsUnimodularSol (W.map ρ) ((W.map ρ).toProjective.neg P),
          ptHom W ρ P hP ≫ (GrpObj.inv : schemeOver W ⟶ schemeOver W).left = ptHom W ρ _ hN) ∧
      (IsAbelianScheme (schemeOver W) ∧ SmoothOfRelativeDimension 1 (schemeOver W).hom ∧
        (originLB W).IsLB ∧ Out.Rigidified (schemeOver W) (originLB W) ∧
        Out.Sym (schemeOver W) (originLB W) ∧ Out.RelAmple (schemeOver W) (originLB W) ∧
        Out.KTriv (schemeOver W) (originLB W)) ∧
      ∃ v : epsR R ⟶ schemeOver W,
        (∃ h : IsUnimodularSol (W.map (algebraMap R (DualNumber R))) ![DualNumber.eps, -1, 0],
          v.left = ptHom W (algebraMap R (DualNumber R)) ![DualNumber.eps, -1, 0] h) ∧
        IsLieBasis ![v] := by
  obtain ⟨inst, hc, hη, hadd, hneg⟩ := GlobalTheory.T.exists_commGrpObj_weierstrassScheme R W hΔ
  exact ⟨inst, hc, hη, hadd, hneg, polarised_of_grpObj R W hΔ hc hη,
    GlobalTheory.WeierstrassLie.isLieBasis_eps R W hη⟩

theorem exists_polAV : ∀ (R : Type) [CommRing R] (W : _root_.WeierstrassCurve R), IsUnit W.Δ →
    ∃ (P : Out.PolAV (Sp R)) (ψ : P.A.left ⟶ scheme W) (v : epsR R ⟶ P.A), P.g = 1 ∧ IsIso ψ ∧
      ψ ≫ toSpec W = P.A.hom ∧ eSec P.A ≫ ψ = zero W ∧
      (∃ h : IsUnimodularSol (W.map (algebraMap R (DualNumber R))) ![DualNumber.eps, -1, 0],
        v.left ≫ ψ = ptHom W (algebraMap R (DualNumber R)) ![DualNumber.eps, -1, 0] h) ∧
      IsLieBasis ![v] := by
  intro R _ W hΔ
  obtain ⟨inst, hc, hη, -, -, ⟨hab, hsm, hlb, hrig, hsym, hamp, hk⟩, v, ⟨h, hv⟩, hbasis⟩ :=
    exists_grpObj_polarised R W hΔ
  let P : Out.PolAV (Sp R) :=
    { A := schemeOver W
      grp := inst
      isAb := hab
      g := 1
      smoothDim := hsm
      L := originLB W
      isLB := hlb
      rigid := hrig
      sym := hsym
      ample := hamp
      ktriv := hk }
  refine ⟨P, 𝟙 _, v, rfl, inferInstance, ?_, ?_, ⟨h, ?_⟩, hbasis⟩
  · rw [Category.id_comp]
    rfl
  · rw [Category.comp_id]
    exact hη
  · rw [Category.comp_id]
    exact hv

end GlobalTheory.WeierstrassCurve
