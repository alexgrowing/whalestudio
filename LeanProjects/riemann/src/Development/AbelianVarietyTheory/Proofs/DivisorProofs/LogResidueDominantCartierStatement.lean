import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogResidueDominantCartier
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.AdjKltOfLtDisc
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_residue_dominant_cartier : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (x : Fin n → X.functionField) (m : ℕ) (g : X.functionFieldˣ) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y) (y : X) (σ : Y) (S : DivOver p) (S' : DivOver (s ≫ p)), TrBasis (Cartier.constFn p) x → 0 < m → IsLogRes p n (dForm (Cartier.constFn p) x) m (CartierDiv.principal g) s K B → DivOver.Over s S' S → S'.IsAt σ → (pullCart s (CartierDiv.principal g) - m • K).mult σ = m → AdjKlt (Cartier.constFn p) n (locRing y) (placeEquiv p S) (dForm (Cartier.constFn p) x) (Finsupp.single (g : X.functionField) (1 / (m : ℚ))) → ∀ v w : Y, v ≠ σ → v ⤳ w → σ ⤳ w → s w ⤳ y → (pullCart s (CartierDiv.principal g) - m • K).mult v < m := by
  first | exact @GlobalTheory.FieldPair.mult_lt_of_adjKlt | exact GlobalTheory.FieldPair.mult_lt_of_adjKlt | (intros; apply GlobalTheory.FieldPair.mult_lt_of_adjKlt <;> assumption)
