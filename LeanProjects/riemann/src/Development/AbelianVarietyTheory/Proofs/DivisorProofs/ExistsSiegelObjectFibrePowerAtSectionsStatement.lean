import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelObjectFibrePowerAtSections
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_siegelObject_fibrePower_at_sections : ∀ {o : Type} [CommRing o] {ζ : o} {h n : ℕ} (F : SFam h n ζ) {S S₀ : Scheme.{0}} (g : S ⟶ S₀) (s' : S ⟶ Sp o) (x : S ⟶ F.X), x ≫ F.s = s' → ∀ (c : SiegPre h n ζ s'), SiegPB c F.univ x → ∀ (A₀ : Over S₀) [GrpObj A₀] [IsCommMonObj A₀] (Q : LB (G2 A₀).left) (β : c.A.left ⟶ A₀.left) (β₂ : (G2 c.A).left ⟶ (G2 A₀).left), IsGrpPullback c.A A₀ g β → IsSquare β β₂ → LBIso c.P (Q.pull β₂) → ∀ (r : ℕ) (d : Fin r → (𝟙_ (Over S) ⟶ c.A)), ∃ (v : S ⟶ (GlobalTheory.LowChart.powA F r).left) (hs : v ≫ GlobalTheory.LowChart.toO F r = s') (β₁ : (GlobalTheory.LowChart.siegAt F v s' hs).A.left ⟶ A₀.left) (β₁₂ : (G2 (GlobalTheory.LowChart.siegAt F v s' hs).A).left ⟶ (G2 A₀).left), IsGrpPullback (GlobalTheory.LowChart.siegAt F v s' hs).A A₀ g β₁ ∧ IsSquare β₁ β₁₂ ∧ LBIso (GlobalTheory.LowChart.siegAt F v s' hs).P (Q.pull β₁₂) ∧ ∀ a, (GlobalTheory.LowChart.cAt F v s' hs a).left ≫ β₁ = (∏ i, d i ^ a i).left ≫ β := by
  first | exact @GlobalTheory.LowChart.exists_siegAt_of_siegPB | exact GlobalTheory.LowChart.exists_siegAt_of_siegPB | (intros; apply GlobalTheory.LowChart.exists_siegAt_of_siegPB <;> assumption)
