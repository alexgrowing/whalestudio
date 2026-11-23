import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsTripleOfAbelianModelDedekind
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem lbIso_lam_pull_of_isGrpPullback : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] (G₁ : Over S') [GrpObj G₁] [IsCommMonObj G₁] (β : G₁.left ⟶ G.left), IsGrpPullback G₁ G f β → ∃ β₂ : (G2 G₁).left ⟶ (G2 G).left, Geo.Tor.IsSquare β β₂ ∧ ∀ (L : LB G.left) (N : LB G₁.left) (X : Scheme.{0}) (Q : LB X) (h : (G2 G).left ⟶ X), L.IsLB → N.IsLB → Q.IsLB → LBIso N (L.pull β) → LBIso (abelian₂ G L) (Q.pull h) → LBIso (abelian₂ G₁ N) (Q.pull (β₂ ≫ h)) := by
  intro S S' f G _ _ G₁ _ _ β hpb
  let U : Over.mk ((G2 G₁).hom ≫ f) ⟶ G2 G := lift (pushPt hpb.1.w (fst G₁ G₁)) (pushPt hpb.1.w (snd G₁ G₁))
  have hU1 : U ≫ fst G G = pushPt hpb.1.w (fst G₁ G₁) := lift_fst _ _
  have hU2 : U ≫ snd G G = pushPt hpb.1.w (snd G₁ G₁) := lift_snd _ _
  refine ⟨U.left, ⟨congrArg (fun z => z.left) hU1, congrArg (fun z => z.left) hU2⟩, ?_⟩
  intro L N X Q h hL hN hQ hNL hLam
  have hx : ∀ i, pushPt hpb.1.w (x2 G₁ i) = U ≫ x2 G i := by
    intro i
    fin_cases i
    · exact hU1.symm
    · exact hU2.symm
  have e₁ : LBIso ((abelian₂ G L).pull U.left) (abelian₂ G₁ N) :=
    GlobalTheory.CM.TripleModel.lbIso_cube_pull hpb hL hN hNL.symm (x2 G₁) (x2 G) U hx
  have hLamL : (abelian₂ G L).IsLB := DVR.linComb_isLB _ hL _ _
  have e₂ : LBIso ((abelian₂ G L).pull U.left) (Q.pull (U.left ≫ h)) :=
    LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (abelian₂ G L) U.left U.left rfl)
      (chartPullSame Q (fun _ => U.left ≫ h) (fun _ => h) (fun _ => 1) U.left fun _ => rfl) hLam
  exact LBIso.trans (DVR.linComb_isLB _ hN _ _) (pull_isLB hLamL _) (pull_isLB hQ _) e₁.symm e₂

end GlobalTheory.Mum
