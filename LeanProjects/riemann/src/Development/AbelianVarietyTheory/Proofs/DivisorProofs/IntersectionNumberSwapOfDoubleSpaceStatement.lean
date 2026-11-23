import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberSwapOfDoubleSpace
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersectionNumber_swap_of_doubleSpace : ∀ (F : Type) [Field F] (Y : Var F) (W : Dbl Y), W.Small → ∀ (κ : Type) (a b : κ), a ≠ b → ∀ (gr : κ → Y.Dv) (D₁ D₂ : κ → CartierDiv W.Z) (Θ : CartierDiv W.Z), (∀ x, IsPull W.p₁ (D₁ x) (gr x)) ∧ (∀ x, IsPull W.p₂ (D₂ x) (gr x)) ∧ (∀ x, x ≠ a → x ≠ b → toPic (D₁ x) = toPic (D₂ x)) ∧ toPic (D₁ a) + toPic (D₁ b) = toPic (D₂ a) + toPic (D₂ b) ∧ toPic Θ = toPic (D₂ b) - toPic (D₁ a) ∧ Θ.Eff ∧ (Θ.supp : Set W.Z) = Set.range W.δ → ∀ Q : MvPolynomial κ ℝ, Y.interPoly gr (rename (Equiv.swap a b) Q) = - Y.interPoly gr Q := by
  first | exact @GlobalTheory.FlagPush.Dbl.interPoly_rename_swap | exact GlobalTheory.FlagPush.Dbl.interPoly_rename_swap | (intros; apply GlobalTheory.FlagPush.Dbl.interPoly_rename_swap <;> assumption)
