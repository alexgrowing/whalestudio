import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftedFunctionOnLogResolution
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lifted_function_on_logResolution : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (η : RatForms p n) (m : ℕ) (G N : CartierDiv X) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y) (F : CartierDiv Y), IsLogRes p n η m G s K B → (∀ U : X.Opens, IsAffineOpen U → Subsingleton (cohOn (twist (GlobalTheory.structureModule Y) (toLB (pullCart s N - F))) (s ⁻¹ᵁ U) 1)) → ∀ (y : X) (σ : Y), (∀ v w : Y, v ≠ σ → v ⤳ w → σ ⤳ w → s w ⤳ y → F.mult v ≤ 0) → s σ ⤳ y → Order.coheight σ = 1 → ∃ h : Y.functionField, (-F).RegularAt σ (h - 1) ∧ ∀ v : Y, v ≠ σ → Order.coheight v = 1 → s v ⤳ y → (-F).RegularAt v h := by
  first | exact @GlobalTheory.PairStep.exists_lifted_fn | exact GlobalTheory.PairStep.exists_lifted_fn | (intros; apply GlobalTheory.PairStep.exists_lifted_fn <;> assumption)
