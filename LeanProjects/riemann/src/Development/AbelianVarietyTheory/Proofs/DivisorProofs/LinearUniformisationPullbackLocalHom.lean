import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PullData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationBaseChangeOfKernelInGeneratingOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActsOnThickeningsOfPullbackUniformisationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearRingActionGenericFibreOfActsAsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedGroupsBaseChange
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusEndOfPadd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinHomIffLinEnd
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem GlobalTheory.Mum.ulin_pull : ∀ (R V : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing V] [IsDomain V] [IsLocalRing V] (θ : R →+* V), Base R → Base V → IsLocalHom θ → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (oA : A.OAct O) (oG : RingAct G O), U.toUnifPre.OLinear O o oA oG → ∀ W : (Sp R).Opens, (∀ y, PsiUnitOn D.toPre y W) → spMap θ (genericPoint (Sp V)) ∈ W → ∃ (D₁ : DegData V (maximalIdeal V)) (hD : IsPullDeg θ D.toPre D₁.toPre) (A₁ : PolAV (Sp (FractionRing V))) (U₁ : Unif (maximalIdeal V) D₁ A₁ ((Over.pullback (specOf θ)).obj G)) (_ : Module O D₁.toPre.X) (o₁ : D₁.toPre.OAct O) (oA₁ : A₁.OAct O) (oG₁ : RingAct ((Over.pullback (specOf θ)).obj G) O), LBIso U₁.LG.L (U.LG.L.pull (pullback.fst G.hom (specOf θ))) ∧ (∀ (a : O) (y : D₁.toPre.X), hD.xe (a • y) = a • hD.xe y) ∧ (∀ a, (o₁.onB.act a).left ≫ GlobalTheory.PsiEvenPull.proj hD = GlobalTheory.PsiEvenPull.proj hD ≫ (o.onB.act a).left) ∧ (∀ a, oG₁.act a = (Over.pullback (specOf θ)).map (oG.act a)) ∧ U₁.toUnifPre.OLinear O o₁ oA₁ oG₁ := by
  intro R V _ _ _ _ _ _ θ bR bV hθ D A G _ _ hG U O _ _ _ o oA oG lin W hψ hW
  have mR : IsMonHom (Iso.refl ((Over.pullback (specOf θ)).obj G)).hom := by show IsMonHom (𝟙 _); infer_instance
  obtain ⟨D₁, A₁, hD, U₁, hU⟩ := GlobalTheory.Mum.unif_baseChange_of_psiUnitOn R bR D A G hG U V bV.1 θ hθ W hψ hW _ (Iso.refl _) mR
  obtain ⟨m, o₁, hx, ho⟩ := GlobalTheory.FactorPull.degAct_pull GlobalTheory.firstFiveLaws.1.globalFns R V θ _ _ hD O o
  obtain ⟨oA₁, lin₁⟩ := GlobalTheory.T.exists_linear_ringAction_genericFibre_of_actsAs V bV D₁ A₁ _ (IsSemiAbelian.pullback _ G hG) U₁ O o₁ (GlobalTheory.FactorPull.ringActPull (specOf θ) oG) fun a =>
    GlobalTheory.T.actsOnThickenings_of_pullback_uniformisation R V θ _ _ D D₁ hD A A₁ G _ (Iso.refl _) U U₁ hU (o.onB.act a) (fun χ => star a • χ) (oG.act a) _ _ _ (o₁.onB.hom a)
      (fun e => ⟨lin.q_lin e a, lin.i_lin e a⟩) ((Category.comp_id _).trans (Category.id_comp _).symm) (ho a) (hx (star a))
  obtain ⟨wL, hwL, -⟩ := hU.lg
  refine ⟨D₁, hD, A₁, U₁, m, o₁, oA₁, _, ?_, hx, fun a => GlobalTheory.PullLinear.act_proj _ hD.e.hom (ho a), fun _ => rfl, lin₁⟩
  have H : LBIso _ _ := ⟨wL, hwL⟩
  rwa [show (Iso.refl ((Over.pullback (specOf θ)).obj G)).hom.left ≫ pullback.fst G.hom (specOf θ) = pullback.fst G.hom (specOf θ) from Category.id_comp _] at H
