import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinHomIffLinEnd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedGroupsBaseChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

noncomputable section

namespace GlobalTheory.MumFam

open GlobalTheory.HalfBC in

theorem refAt_pull : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R'), Function.Injective ρ → ∀ (I : Ideal R) (D : DegData R I) (D' : DegPre R') (hD : IsPullDeg ρ D.toPre D'), RefAt (pol D) ρ D' hD.xe (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf ρ)) := by
  intro R R' _ _ _ _ ρ hρ I D D' hD
  letI := D'.P.isAb.comm
  have gp := pull_grp hD
  refine ⟨sqOf gp, lamIso gp hD.w, gp, isSquare_sqOf gp, isGen_lamIso gp hD.w hD.w_gen, fun a => hD.c_pr a,
    fun κ hκ a b z J J' hJ hJ' => ?_⟩
  obtain rfl : κ = GlobalTheory.ArcPull.genMap hρ := by
    have : Mono (jK R) := Wit.mono_jK
    refine (cancel_mono (jK R)).1 (hκ.trans ?_)
    rw [← GlobalTheory.ArcPull.fracMap_sq hρ, Category.id_comp]
  rw [← GlobalTheory.FactorPull.tau_lam hD hρ a b hJ hJ']
  refine congrArg₂ (· * ·) ?_ ((Wit.exists_tau D.toPre (hD.xe a) (hD.xe b)).choose_spec.2 _ _ z J hJ).symm
  symm
  show gw (lamIso gp hD.w) _ z (fun I => J (_ ≫ sqOf gp ≫ GlobalTheory.PrimCocycle.lamφ D.toPre.P.A I))
    (fun I => J' (_ ≫ GlobalTheory.PrimCocycle.lamφ D'.P.A I)) = _
  refine (gw_lamIso gp hD.w _ z _ _ (fun I => by
      have := hJ ((lift (toUnit (TK R') ≫ D'.c a) (toUnit (TK R') ≫ D'.c b)).left ≫ sqOf gp ≫ GlobalTheory.PrimCocycle.lamφ D.toPre.P.A I)
      erw [← pt_sqOf gp I]
      exact this) (fun I => hJ' _)).trans ?_
  refine Finset.prod_congr rfl fun I _ => ?_
  show _ = gw hD.w _ z _ _ ^ _
  erw [Category.assoc, ← sqOf_lamφ gp I]
  rfl

end GlobalTheory.MumFam
