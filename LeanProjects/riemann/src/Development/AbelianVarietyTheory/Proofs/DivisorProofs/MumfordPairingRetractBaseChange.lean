import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PullData
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

namespace GlobalTheory.Mum

open GlobalTheory.HalfBC GlobalTheory.PullLinear GlobalTheory.FactorPull in

theorem lamRetract_baseChange : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] (G₀ : Over S) [GrpObj G₀] [IsCommMonObj G₀] (inc : G ⟶ G₀) (v : G₀ ⟶ G₀) (L : LB G₀.left) (L₁ : LB ((Over.pullback f).obj G₀).left) (P : LB (G2 G).left), L.IsLB → L₁.IsLB → P.IsLB → LBIso L₁ (L.pull (pullback.fst G₀.hom f)) → LBIso P ((abelian₂ G₀ L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ v) : G2 G ⟶ G2 G₀).left) → ∃ π₂ : (G2 ((Over.pullback f).obj G)).left ⟶ (G2 G).left, IsSquare (G' := (Over.pullback f).obj G) (G := G) (pullback.fst G.hom f) π₂ ∧ LBIso ((abelian₂ ((Over.pullback f).obj G₀) L₁).pull (lift (fst _ _ ≫ (Over.pullback f).map inc) (snd _ _ ≫ (Over.pullback f).map inc ≫ (Over.pullback f).map v) : G2 ((Over.pullback f).obj G) ⟶ G2 ((Over.pullback f).obj G₀)).left) (P.pull π₂) := by
  intro S S' f G _ _ G₀ _ _ inc v L L₁ P hL hL₁ hP hw hPw
  have gG := isGrpPullback_pullback G f
  have gG' := isGrpPullback_pullback G₀ f
  obtain ⟨wL, hwL⟩ := hw
  refine ⟨sqOf gG, isSquare_sqOf gG, ?_⟩
  have hm := lift_sq gG gG' (u := inc) (v := inc ≫ v) (u₁ := (Over.pullback f).map inc)
    (v₁ := (Over.pullback f).map inc ≫ (Over.pullback f).map v) (map_left_fst _ _)
    (by rw [← CategoryTheory.Functor.map_comp]; exact map_left_fst _ _)
  have H : LBIso _ _ := ⟨lamIso gG' wL, isGen_lamIso gG' wL hwL⟩
  have lL : (abelian₂ G₀ L).IsLB := DVR.linComb_isLB _ hL _ _
  have lL₁ : (abelian₂ _ L₁).IsLB := DVR.linComb_isLB _ hL₁ _ _
  have H₁ := H.chartPull (Geo.Tor.chartPullPull _ _ _ rfl)
    (chartPullLinComb (abelian₂ G₀ L) _ (fun _ => sqOf gG) (fun _ => sqOf gG') _ _ fun _ => hm.symm)
  have H₂ := hPw.chartPull (Geo.Tor.chartPullPull _ (sqOf gG) _ rfl) (Geo.Tor.chartPullPull _ (sqOf gG) _ rfl)
  exact LBIso.trans (pull_isLB lL₁ _) (pull_isLB (pull_isLB lL _) _) (pull_isLB hP _) H₁ H₂.symm

end GlobalTheory.Mum
