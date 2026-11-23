import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Poinc.SquareIso

theorem lbIso_pull_further {X Y Z : Scheme.{0}} {L : LB X} {M : LB Y} {a : Y ⟶ X} (h : LBIso M (L.pull a)) (j : Z ⟶ Y)
    {a' : Z ⟶ X} (e : a' = j ≫ a) : LBIso (M.pull j) (L.pull a') :=
  LBIso.chartPull (Geo.Tor.chartPullPull M j j rfl) (Geo.Tor.chartPullSame L _ (fun _ => a) _ j fun _ => e) h

theorem iso_pull_of_square : ∀ {X Y Z Y' : Scheme.{0}} (LA' : LB X) (LA : LB Y) (L₁ : LB Z) (L₂ : LB Y') (ψ : X ⟶ Y) (φ₁ : Y ⟶ Z) (φ₂ : X ⟶ Y') (τ : Y' ⟶ Z), LA'.IsLB → LA.IsLB → L₁.IsLB → L₂.IsLB → ψ ≫ φ₁ = φ₂ ≫ τ → (∃ w : LB.Iso LA' (LA.pull ψ), w.IsGen) → (∃ w : LB.Iso LA (L₁.pull φ₁), w.IsGen) → LBIso L₂ (L₁.pull τ) → ∃ w : LB.Iso LA' (L₂.pull φ₂), w.IsGen := by
  intro X Y Z Y' LA' LA L₁ L₂ ψ φ₁ φ₂ τ hA' hA h₁ h₂ e w₁ w₂ w₃
  have a : LBIso (LA.pull ψ) (L₁.pull (φ₂ ≫ τ)) := lbIso_pull_further w₂ ψ e.symm
  have b : LBIso (L₂.pull φ₂) (L₁.pull (φ₂ ≫ τ)) := lbIso_pull_further w₃ φ₂ rfl
  exact LBIso.trans hA' (pull_isLB h₁ _) (pull_isLB h₂ _) (LBIso.trans hA' (pull_isLB hA _) (pull_isLB h₁ _) w₁ a) b.symm

end GlobalTheory.Poinc.SquareIso
