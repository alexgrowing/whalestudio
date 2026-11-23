import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRescaleIsPullDeg
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TraceFormTwistIsoOfPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TauBalOfIsPullDeg
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TauBimultOfIsPullDeg
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsScalarFormTraceForm
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteNormalising
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GtActIffEqGtSmul
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem tauBimult_and_exists_oAct_of_pullDeg : ∀ {O : Type} [CommRing O] [StarRing O] {W V : Type} [CommRing W] [IsDomain W] [CommRing V] [IsDomain V] {θ₀ : W →+* V} {D₀ : DegPre W} [Module O D₀.X] (o₀ : D₀.OAct O) {D : DegPre V} [Module O D.X] (hD : IsPullDeg θ₀ D₀ D) (ob : D.P.OAct O), (∀ (a : O) y, hD.xe (a • y) = a • hD.xe y) → (∀ (a : O) y, D.c (a • y) = D.c y ≫ ob.act a) → (∀ a : O, (ob.act a).left ≫ hD.e.hom.left ≫ pullback.fst D₀.P.A.hom (specOf θ₀) = (hD.e.hom.left ≫ pullback.fst D₀.P.A.hom (specOf θ₀)) ≫ (o₀.onB.act a).left) → D₀.TauBimult → ∀ w0 : O, TraceFormTwistIso D₀ o₀ w0 → D.TauBimult ∧ ∃ o : D.OAct O, o.onB = ob ∧ TraceFormTwistIso D o w0 := by
  intro O _ _ W V _ _ _ _ θ₀ D₀ _ o₀ D _ hD ob hx hcl hact hB w0 hP
  have hG : GlobalFnsSt := GlobalTheory.allSixLaws.1.globalFns
  have hc : ∀ a : O, ob.act a ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf θ₀)).map (o₀.onB.act a) := by
    intro a
    have a₂ : ((Over.pullback (specOf θ₀)).map (o₀.onB.act a)).left ≫ pullback.fst D₀.P.A.hom (specOf θ₀) =
        pullback.fst _ _ ≫ (o₀.onB.act a).left := pullback.lift_fst _ _ _
    refine Over.OverMorphism.ext (pullback.hom_ext ?_ ?_)
    · have h := hact a
      simp only [Over.comp_left, Category.assoc] at h ⊢
      exact h.trans (congrArg (fun q => hD.e.hom.left ≫ q) a₂.symm)
    · exact (Over.w (ob.act a ≫ hD.e.hom)).trans
        (Over.w (hD.e.hom ≫ (Over.pullback (specOf θ₀)).map (o₀.onB.act a))).symm
  let o : D.OAct O := ⟨ob, hcl, fun a =>
    GlobalTheory.tauBal_of_isPullDeg hG _ _ θ₀ D₀ D hD (o₀.onB.act a) (o₀.onB.act (star a)) (ob.act a) (ob.act (star a))
      (o₀.onB.hom _) (o₀.onB.hom _) (o₀.onB.rosati a) (hc a) (hc (star a)) (fun y => a • y) (fun y => star a • y)
      (fun y => a • y) (fun y => star a • y) (hx a) (hx (star a)) (o₀.c_lin a) (o₀.c_lin (star a)) (o₀.tau_bal a)⟩
  exact ⟨GlobalTheory.TauPull.tauBimult_pull hG hD hB, o, rfl,
    GlobalTheory.traceFormTwistIso_of_overPullback _ _ θ₀ D₀ D hD O o₀ o hx hc w0 hP⟩

end GlobalTheory
