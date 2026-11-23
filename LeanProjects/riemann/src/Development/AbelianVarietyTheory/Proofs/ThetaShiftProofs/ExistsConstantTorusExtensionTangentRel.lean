import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsAdicCompleteIdealEps
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsGtPtGenRelRField

namespace GlobalTheory.ConstTan

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

theorem exists_tanRel : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (ν : Out.GtPt a.D₀ (epsR ℂ)), ∃ g₁ : Out.GtPt W.P.D.toPre (epsR ℂ⟦X⟧), TanRel W ν g₁ := by
  intro _ E _ _ _ H _ D l Xo c O _ β Y _ _ b a χ W ν
  haveI := isLocalRing_dual ℂ⟦X⟧
  obtain ⟨gp, hw, -, -, hc, -⟩ := W.spec
  obtain ⟨g, hg⟩ := ConstPoint.exists_gtPt_genRelR (A := DualNumber ℂ⟦X⟧) globalFns_holds gp hw
    W.e.symm.toAddEquiv.toAddMonoidHom
    (fun y => by have := hc (W.e.symm y); rwa [LinearEquiv.apply_symm_apply] at this)
    (T := epsR ℂ) (spMap (algebraMap ℂ⟦X⟧ (DualNumber ℂ⟦X⟧))) (spMap constEps)
    ((spMap_comp _ _).symm.trans ((congrArg spMap (RingHom.ext fun r => dualMapR_inl _ r)).trans (spMap_comp _ _))) ν
  refine ⟨g, fun x => ?_⟩
  have := hg (W.e x)
  rw [show W.e.symm.toAddEquiv.toAddMonoidHom (W.e x) = x from W.e.symm_apply_apply x] at this
  exact this

end GlobalTheory.ConstTan
