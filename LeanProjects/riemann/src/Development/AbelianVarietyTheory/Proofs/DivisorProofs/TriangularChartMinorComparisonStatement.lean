import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriangularChartMinorComparison
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNonarchimedeanW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullFrameRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FnEquivApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColMinorEqSupMinors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinorsTriangularChangeInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeftInverseRegularOfRegularStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodReductionExtendsRegular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgebraicPointSpecializing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitAtPointsOverPrimeBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReductionRegularFunctionsGoodPrimesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnMinorNormInequalityStatement
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.WholeFlag GlobalTheory.ConstLat GlobalTheory.WholeFlag.Glue GlobalTheory.ConstLat.CramerFrame
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.triangular_chart_minor_comparison : ∀ {F : Type} [Field F] [NumberField F] {Y : Var F} (V : Cover Y) (W : Y.X.Opens) (p : ℕ), p.Prime → genericPoint Y.X ∈ W → ∀ {g : ℕ} (U' : V.X.Opens) (H : Matrix (Fin (g + g)) (Fin g) V.G.functionField) (d : Y.X → Fin g → Y.Fnˣ) (T : Y.X → Matrix (Fin g) (Fin g) Y.Fn) (σ : ∀ k : ℕ, Fin k → Fin (g + g)), (∀ y, (T y).BlockTriangular id ∧ ∀ i, T y i i = (d y i : Y.Fn)) → ChartReg V U' H T → (∀ (k : ℕ) (hk : k ≤ g), minorAt H k hk (σ k) ≠ 0) → (∀ z : V.G, V.j z ∈ U' → ∀ (k : ℕ) (hk : k ≤ g), UnitAt z (minorAt (H * ((T (V.π z)).map V.φ)⁻¹) k hk (σ k))) → (AtTest V W p fun _ e y z yt => ⊤ ≤ yt ⁻¹ᵁ U' → ∀ (k : ℕ) (hk : k ≤ g) (τ : Fin k → Fin (g + g)), e.w (minorAt (valMat V H (T (below y.1)) z) k hk τ) ≤ e.w (minorAt (valMat V H (T (below y.1)) z) k hk (σ k))) → (rowSel (σ g) * frameUm V H σ).det = 1 ∧ ∀ x ∈ U', ¬ IsUnit (p : V.X.presheaf.stalk x) → ∀ r k, RegAt x (frameUm V H σ r k) := by
  first | exact @GlobalTheory.ConstLat.CramerFrame.frameUm_det_regAt | exact GlobalTheory.ConstLat.CramerFrame.frameUm_det_regAt | (intros; apply GlobalTheory.ConstLat.CramerFrame.frameUm_det_regAt <;> assumption)
