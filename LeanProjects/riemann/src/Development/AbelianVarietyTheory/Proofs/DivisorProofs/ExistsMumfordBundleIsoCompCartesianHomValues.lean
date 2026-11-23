import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinesPolarisedDataBaseChangeSymmetric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoNormalisedRespectsLaws
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsoEqOfMapsAlongSection
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HalfBC GlobalTheory.PrimCocycle

namespace GlobalTheory.TautPull

theorem lamIso_comp_exists : ∀ {S S' S₁ : Scheme.{0}} {B : Over S₁} {G : Over S} {G' : Over S'} [GrpObj B] [IsCommMonObj B] [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] {M : LB B.left} {L : LB G.left} {L' : LB G'.left} {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (gp : IsGrpPullback G' G f φ) {β₂ : (G2 G).left ⟶ (G2 B).left}, M.IsLB → L.IsLB → L'.IsLB → ∀ (w : LB.Iso (abelian₂ G L) ((abelian₂ B M).pull β₂)) (v : LB.Iso L' (L.pull φ)), w.IsGen → v.IsGen → ∃ w'' : LB.Iso (abelian₂ G' L') ((abelian₂ B M).pull (sqOf gp ≫ β₂)), w''.IsGen ∧ ∀ (Z : Scheme.{0}) (p : Z ⟶ (G2 G').left) (z : Z) (J : (Z ⟶ B.left) → M.ι) (J₁ : (Z ⟶ G.left) → L.ι) (J' : (Z ⟶ G'.left) → L'.ι), Good M z J → Good L z J₁ → Good L' z J' → lamVal w'' p z J J' = lamVal w (p ≫ sqOf gp) z J J₁ * ∏ I, gw v (p ≫ lamφ G' I) z (J₁ ((p ≫ lamφ G' I) ≫ φ)) (J' (p ≫ lamφ G' I)) ^ lamε I := by
  intro S S' S₁ B G G' _ _ _ _ _ _ M L L' f φ gp β₂ hM hL hL' w v hw hv
  have hΛB : (abelian₂ B M).IsLB := DVR.linComb_isLB _ hM _ _
  have hΛ : (abelian₂ G L).IsLB := DVR.linComb_isLB _ hL _ _
  have hΛ' : (abelian₂ G' L').IsLB := DVR.linComb_isLB _ hL' _ _
  obtain ⟨w'', T⟩ := exists_comp hΛ w (lamIso gp v) ((isGen_iff _).1 hw)
    (pgen_lamIso gp v ((isGen_iff v).1 hv)) hΛB hΛ'
  refine ⟨w'', (isGen_iff _).2 (T.pgen_comp hΛ ((isGen_iff _).1 hw)
    (pgen_lamIso gp v ((isGen_iff v).1 hv))), ?_⟩
  intro Z p z J J₁ J' hJ hJ₁ hJ'
  have t := T Z p z (fun I => J (p ≫ (sqOf gp ≫ β₂) ≫ lamφ B I))
    (fun I => J₁ ((p ≫ sqOf gp) ≫ lamφ G I)) (fun I => J' (p ≫ lamφ G' I))
    (Set.mem_iInter.2 fun I => hJ (p ≫ (sqOf gp ≫ β₂) ≫ lamφ B I))
    (Set.mem_iInter.2 fun I => hJ₁ ((p ≫ sqOf gp) ≫ lamφ G I))
    (Set.mem_iInter.2 fun I => hJ' (p ≫ lamφ G' I))
  refine t.trans (congrArg₂ (· * ·) ?_ ?_)
  · show _ = gw w (p ≫ sqOf gp) z (fun I => J ((p ≫ sqOf gp) ≫ β₂ ≫ lamφ B I))
      (fun I => J₁ ((p ≫ sqOf gp) ≫ lamφ G I))
    simp only [Category.assoc]
  · rw [gw_lamIso gp v p z _ _ (fun I => by
      have := hJ₁ ((p ≫ sqOf gp) ≫ lamφ G I)
      rw [Category.assoc, sqOf_lamφ, ← Category.assoc] at this ⊢
      exact this) (fun I => hJ' (p ≫ lamφ G' I))]
    refine Finset.prod_congr rfl fun I _ => ?_
    rw [Category.assoc, sqOf_lamφ, ← Category.assoc]

end GlobalTheory.TautPull
