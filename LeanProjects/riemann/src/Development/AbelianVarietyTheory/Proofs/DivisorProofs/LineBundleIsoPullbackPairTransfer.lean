import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomProdPow
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj

namespace GlobalTheory.PullIsoCongr

theorem lbIso_pull_congr (X Y : Scheme.{0}) (Q₁ Q₂ : LB X) (m m' : Y ⟶ X) (h₁ : Q₁.IsLB) (h₂ : Q₂.IsLB)
    (e : LBIso Q₁ Q₂) (f : LBIso (Q₁.pull m) (Q₁.pull m')) : LBIso (Q₂.pull m) (Q₂.pull m') := by
  have a : LBIso (Q₂.pull m) (Q₁.pull m) :=
    LBIso.chartPull (chartPullPull Q₂ m m rfl) (chartPullPull Q₁ m m rfl) (LBIso.symm e)
  have b : LBIso (Q₁.pull m') (Q₂.pull m') :=
    LBIso.chartPull (chartPullPull Q₁ m' m' rfl) (chartPullPull Q₂ m' m' rfl) e
  exact LBIso.trans (pull_isLB h₂ m) (pull_isLB h₁ m') (pull_isLB h₂ m')
    (LBIso.trans (pull_isLB h₂ m) (pull_isLB h₁ m) (pull_isLB h₁ m') a f) b

theorem isocongr : ∀ (X Y : Scheme.{0}) (Q₁ Q₂ : LB X) (m m' : Y ⟶ X), Q₁.IsLB → Q₂.IsLB → LBIso Q₁ Q₂ → LBIso (Q₁.pull m) (Q₁.pull m') → LBIso (Q₂.pull m) (Q₂.pull m') :=
  fun X Y Q₁ Q₂ m m' h₁ h₂ e f => lbIso_pull_congr X Y Q₁ Q₂ m m' h₁ h₂ e f

end GlobalTheory.PullIsoCongr
