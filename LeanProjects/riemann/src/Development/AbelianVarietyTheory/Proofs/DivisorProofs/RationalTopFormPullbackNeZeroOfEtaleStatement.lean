import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalTopFormPullbackNeZeroOfEtale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldMapCompConstFn
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalTopFormPullback_ne_zero_of_etale : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] [IsLocallyNoetherian M] [IsLocallyNoetherian W] (p : W ⟶ Sp ℂ) (f : M ⟶ W) [IsDominant f] (n : ℕ) [SmoothOfRelativeDimension n p] [SmoothOfRelativeDimension n (f ≫ p)] (U : M.Opens), Etale (U.ι ≫ f) → (U : Set M).Nonempty → ∀ η : RatForms p n, η ≠ 0 → GlobalTheory.EtaleKlt.ratPull p f n η ≠ 0 := by
  first | exact @GlobalTheory.EtaleKlt.ratPull_ne_zero | exact GlobalTheory.EtaleKlt.ratPull_ne_zero | (intros; apply GlobalTheory.EtaleKlt.ratPull_ne_zero <;> assumption)
