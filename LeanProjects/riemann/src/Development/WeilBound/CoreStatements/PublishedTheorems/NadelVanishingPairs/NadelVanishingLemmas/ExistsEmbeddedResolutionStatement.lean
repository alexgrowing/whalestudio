import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsEmbeddedResolution
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.exists_embedded_resolution : GlobalTheory.Published.Principalisation → ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (n : ℕ) (η : RatForms p n) (m : ℕ) (G : CartierDiv X), η ≠ 0 → ∀ (Y₀ : Scheme.{0}) [IsIntegral Y₀] (s₀ : Y₀ ⟶ X) [IsDominant s₀], SmoothOfRelativeDimension n (s₀ ≫ p) → IsProjOver (s₀ ≫ p) → Function.Bijective (functionFieldMap s₀) → ∀ (Z : Closeds Y₀), Z ≠ ⊤ → ∀ (A : LB Y₀) (hA : IsAmpleLB A), ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (t : Y ⟶ Y₀) (_ : IsDominant t) (K : CartierDiv Y) (B : Closeds Y), IsLogRes p n η m G (t ≫ s₀) K B ∧ (∀ y, t y ∈ Z → y ∈ B) ∧ ∃ (c : ℕ) (E : CartierDiv Y) (A₁ : LB Y) (hA₁ : IsAmpleLB A₁), 0 < c ∧ E.Eff ∧ E.supp ≤ B ∧ c • CechPic.pull t (cls A hA.isLB) = cls A₁ hA₁.isLB + toPic E := by
  first | exact @_root_.GlobalTheory.exists_logRes_ample | exact _root_.GlobalTheory.exists_logRes_ample | (intros; apply _root_.GlobalTheory.exists_logRes_ample <;> assumption)
