import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinorsTriangularChangeInvariant
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNonarchimedeanW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullFrameRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FnEquivApply
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.WholeFlag GlobalTheory.ConstLat GlobalTheory.WholeFlag.Glue GlobalTheory.ConstLat.CramerFrame
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.minors_triangular_change_invariant : ∀ {K : Type} [Field K] {g : ℕ} (H : Matrix (Fin (g + g)) (Fin g) K) (Tm : Matrix (Fin g) (Fin g) K), Tm.BlockTriangular id → (∀ i, Tm i i ≠ 0) → ∀ (σ : ∀ k : ℕ, Fin k → Fin (g + g)), (∀ (k : ℕ) (hk : k ≤ g) (τ : Fin k → Fin (g + g)), minorAt H k hk τ = minorAt (H * Tm⁻¹) k hk τ * ∏ i : Fin k, Tm (Fin.castLE hk i) (Fin.castLE hk i)) ∧ cramerCol H σ = cramerCol (H * Tm⁻¹) σ ∧ ((∀ (k : ℕ) (hk : k ≤ g), minorAt (H * Tm⁻¹) k hk (σ k) ≠ 0) → ∀ i : Fin g, (frameC H σ i : K) = Tm i i * minorAt (H * Tm⁻¹) ((i : ℕ) + 1) i.2 (σ ((i : ℕ) + 1)) / minorAt (H * Tm⁻¹) i i.2.le (σ i)) := by
  first | exact @GlobalTheory.ConstLat.CramerFrame.triChange | exact GlobalTheory.ConstLat.CramerFrame.triChange | (intros; apply GlobalTheory.ConstLat.CramerFrame.triChange <;> assumption)
