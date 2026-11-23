import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsFgForallOverLbIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
namespace GlobalTheory.GenFibreBaseChange

theorem genFibre_pull : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R') (a : FractionRing R →+* FractionRing R'), a.comp (algebraMap R (FractionRing R)) = (algebraMap R' (FractionRing R')).comp ρ → ∀ (G : Over (Sp R)) [GrpObj G], ∃ π₀ : ((Over.pullback (jK R')).obj ((Over.pullback (spMap ρ)).obj G)).left ⟶ ((Over.pullback (jK R)).obj G).left, IsGrpPullback ((Over.pullback (jK R')).obj ((Over.pullback (spMap ρ)).obj G)) ((Over.pullback (jK R)).obj G) (spMap a) π₀ ∧ ∀ L : LB G.left, L.IsLB → LBIso ((L.pull (pullback.fst G.hom (spMap ρ))).pull (pullback.fst (pullback.snd G.hom (spMap ρ)) (jK R'))) ((L.pull (pullback.fst G.hom (jK R))).pull π₀) := by
  intro R R' _ _ _ _ ρ a ha G _
  have hsq : jK R' ≫ spMap ρ = spMap a ≫ jK R := by
    simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ha]
  have hw : (pullback.fst (pullback.snd G.hom (spMap ρ)) (jK R') ≫ pullback.fst G.hom (spMap ρ)) ≫ G.hom =
      (pullback.snd (pullback.snd G.hom (spMap ρ)) (jK R') ≫ spMap a) ≫ jK R := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc, hsq,
      Category.assoc]
  let π₀ : pullback (pullback.snd G.hom (spMap ρ)) (jK R') ⟶ pullback G.hom (jK R) := pullback.lift _ _ hw
  have e₁ : π₀ ≫ pullback.fst G.hom (jK R) =
      pullback.fst (pullback.snd G.hom (spMap ρ)) (jK R') ≫ pullback.fst G.hom (spMap ρ) := pullback.lift_fst _ _ _
  have e₂ : π₀ ≫ pullback.snd G.hom (jK R) = pullback.snd (pullback.snd G.hom (spMap ρ)) (jK R') ≫ spMap a :=
    pullback.lift_snd _ _ _
  refine ⟨π₀, ?_, fun L hL => ?_⟩
  · have n := (isGrpPullback_pullback ((Over.pullback (spMap ρ)).obj G) (jK R')).comp
      (isGrpPullback_pullback G (spMap ρ))
    rw [hsq] at n
    have n' : IsGrpPullback ((Over.pullback (jK R')).obj ((Over.pullback (spMap ρ)).obj G)) G (spMap a ≫ jK R)
        (π₀ ≫ pullback.fst G.hom (jK R)) := by
      rw [e₁]; exact n
    exact IsGrpPullback.cancel (isGrpPullback_pullback G (jK R)) n' e₂
  · have h₁ := GlobalTheory.Spread.lbIso_pull_pull hL (a := pullback.fst G.hom (spMap ρ))
      (pullback.fst (pullback.snd G.hom (spMap ρ)) (jK R')) rfl
    have h₂ := GlobalTheory.Spread.lbIso_pull_pull hL (a := pullback.fst G.hom (jK R)) π₀ e₁.symm
    exact LBIso.trans (pull_isLB (pull_isLB hL _) _) (pull_isLB hL _) (pull_isLB (pull_isLB hL _) _)
      (LBIso.symm h₁) h₂

end GlobalTheory.GenFibreBaseChange
