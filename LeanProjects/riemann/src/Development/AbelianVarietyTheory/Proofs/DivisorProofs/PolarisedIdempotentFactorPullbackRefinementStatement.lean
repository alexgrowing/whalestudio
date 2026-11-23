import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedIdempotentFactorPullbackRefinement
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedGroupsBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleBaseOfCompleteNormalLocalCharZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoSquarePassesSecondIsoStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HalfBC GlobalTheory.PrimCocycle GlobalTheory.ArcPull
open GlobalTheory.PsiEvenPull (proj)
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarisedIdempotentFactor_pullback_refinement : ∀ {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R'), Function.Injective ρ →
  ∀ (Q : Data R) (D' : DegPre R) (F : PFactor Q D') (D : DegPre R') (ε : D.X ≃+ Q.X), Refines Q ρ D ε →
  ∀ (D₁' : DegPre R') (hD' : IsPullDeg ρ D' D₁') [Module F.O D₁'.X] (o₁ : D₁'.OAct F.O),
    (∀ (a : F.O) (y : D₁'.X), hD'.xe (a • y) = a • hD'.xe y) →
    (∀ a, (o₁.onB.act a).left ≫ proj hD' = proj hD' ≫ (F.o.onB.act a).left) →
    ∃ (inc : D.P.A ⟶ D₁'.P.A) (pr : D₁'.P.A ⟶ D.P.A) (xi : D.X →+ D₁'.X) (xp : D₁'.X →+ D.X)
      (w : LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ D₁'.P.A D₁'.P.L).pull
        (lift (fst D.P.A D.P.A ≫ inc) (snd D.P.A D.P.A ≫ inc ≫ o₁.onB.act F.f) : G2 D.P.A ⟶ G2 D₁'.P.A).left)),
      IsMonHom inc ∧ IsMonHom pr ∧ inc ≫ pr = 𝟙 _ ∧ pr ≫ inc = o₁.onB.act F.e ∧ (∀ y, xp (xi y) = y) ∧
      (∀ z, xi (xp z) = F.e • z) ∧ (∀ y, D₁'.c (xi y) = D.c y ≫ inc) ∧
      (Function.Injective fun y => star F.e • F.f • xi y) ∧ (∀ z : D₁'.X, ∃ y, star F.e • z = star F.e • F.f • xi y) ∧
      w.IsGen ∧ ∀ a b z J J', Good D₁'.P.L z J → Good D.P.L z J' →
        val (D.tau a b) (𝟙 _) z J' =
          lamVal w (lift (toUnit (TK R') ≫ D.c a) (toUnit (TK R') ≫ D.c b)).left z J J' *
            val (D₁'.tau (xi a) (F.f • xi b)) (𝟙 _) z J := by
  first | exact @GlobalTheory.FactorPull.pfactor_pull | exact GlobalTheory.FactorPull.pfactor_pull | (intros; apply GlobalTheory.FactorPull.pfactor_pull <;> assumption)
