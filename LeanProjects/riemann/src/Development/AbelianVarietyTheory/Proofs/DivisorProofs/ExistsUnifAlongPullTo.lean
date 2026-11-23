import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMumfordFamOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitPeriodFormValuationSumRefinedChart
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteDvrIntegralClosureFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnifAlongFinite
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT GlobalTheory.ArcPull GlobalTheory.PullLinear

noncomputable section

namespace GlobalTheory.TraitExt

open GlobalTheory.ArcPull in

theorem exists_unifAlong_pullTo : ∀ {g n : ℕ} (F : SFam g n (zetaAway n)) (T : GlobalTheory.Poinc.Trait F) (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂] (f : T.V →+* V₂), IsCN V₂ → IsDiscreteValuationRing V₂ → Function.Injective f → f.Finite → IsLocalHom f → ∃ (D' : DegData V₂ (maximalIdeal V₂)) (_ : IsPullDeg f T.D.toPre D'.toPre) (G' : Over (Sp V₂)) (_ : GrpObj G') (_ : IsCommMonObj G') (π : G'.left ⟶ T.G.left) (A' : PolAV (Sp (FractionRing V₂))) (U' : Unif (maximalIdeal V₂) D' A' G'), IsUnifAlong F T.y (T.U.gen.hom.left ≫ T.α) f π U' := by
  intro g n F T V₂ _ _ _ f hCN _ hinj hfin hloc
  obtain ⟨hN, hIC, hW, hC⟩ := hCN
  have hR : AdmBase T.V (maximalIdeal T.V) := ⟨inferInstance, inferInstance, inferInstance, T.complete⟩
  have hR' : AdmBase V₂ (maximalIdeal V₂) := ⟨hN, inferInstance, hIC, hW⟩
  have hI : (maximalIdeal T.V).map f ≤ maximalIdeal V₂ :=
    Ideal.map_le_iff_le_comap.2 fun a ha => map_nonunit f a ha
  obtain ⟨D', hD, A', U', gA, πK, gpA, tA, hK, hgen⟩ := exists_pull_gen hR hR' f hinj hI T.semi T.U
  obtain ⟨β₂, hβ₂, hΛ⟩ := GlobalTheory.Mum.lbIso_lam_pull_of_isGrpPullback _ _ _ T.A.A A'.A gA gpA
  have sq : spMap (fracMap hinj) ≫ jK T.V = jK V₂ ≫ spMap f :=
    (fracMap_sq hinj).symm.trans (Category.id_comp _)
  refine ⟨D', hD, (Over.pullback (spMap f)).obj T.G, inferInstance, inferInstance, pullback.fst T.G.hom (spMap f),
    A', U', ?_⟩
  refine ⟨isGrpPullback_pullback T.G (spMap f), spMap (fracMap hinj), πK, gA ≫ T.α, β₂ ≫ T.α₂, sq, hK,
    gpA.comp T.cart, isSquare_comp hβ₂ T.sq, hΛ T.A.L A'.L _ F.univ.P T.α₂ T.A.isLB A'.isLB F.univ.isLB tA T.lb, ?_⟩
  rw [← Category.assoc, hgen, Category.assoc]

end GlobalTheory.TraitExt
