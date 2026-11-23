import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartRegularMinorNorms
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
theorem _root_.GlobalTheory.T.chart_regular_minor_norms : ∀ {F : Type} [Field F] [NumberField F] {Y : Var F} {C : CxSt F} {g : ℕ} (A : Fin g → Adl C Y) (p : ℕ), p.Prime → ∀ (V : Cover Y) (W : Y.X.Opens), genericPoint Y.X ∈ W → ∀ (U : V.X.Opens) (H : Matrix (Fin (g + g)) (Fin g) V.G.functionField) (d : Y.X → Fin g → Y.Fnˣ) (T : Y.X → Matrix (Fin g) (Fin g) Y.Fn), (∀ y, (T y).BlockTriangular id ∧ ∀ i, T y i i = (d y i : Y.Fn)) → LineBase V d A p → ChartReg V U H T → MinorNorm V W U H d T A p → ∀ x ∈ U, ¬ IsUnit (p : V.X.presheaf.stalk x) → ∃ (U₁ : V.X.Opens) (m : ℕ) (f : ∀ k : ℕ, (Fin k → Fin (g + g)) → V.X.functionField), 0 < m ∧ U₁ ≤ U ∧ x ∈ U₁ ∧ (∀ (k : ℕ) (hk : k ≤ g) (τ : Fin k → Fin (g + g)) (z : V.G), V.j z ∈ U₁ → RegAt (V.j z) (f k τ) ∧ (UnitAt (V.j z) (f k τ) ↔ UnitAt z (minorAt (H * ((T (V.π z)).map V.φ)⁻¹) k hk τ))) ∧ (AtTest V W p fun _ e y z yt => ⊤ ≤ yt ⁻¹ᵁ U₁ → ∀ (k : ℕ) (hk : k ≤ g), 0 < colMinor e.w (valMat V H (T (below y.1)) z) (Finset.univ.filter fun l : Fin g => (l : ℕ) < k) ∧ ∀ τ : Fin k → Fin (g + g), e.w (valAt (z ≫ V.j) (f k τ)) = (e.w (minorAt (valMat V H (T (below y.1)) z) k hk τ) / colMinor e.w (valMat V H (T (below y.1)) z) (Finset.univ.filter fun l : Fin g => (l : ℕ) < k)) ^ m) := by
  first | exact @GlobalTheory.ConstLat.CramerFrame.MaxFun.exists_maxFun | exact GlobalTheory.ConstLat.CramerFrame.MaxFun.exists_maxFun | (intros; apply GlobalTheory.ConstLat.CramerFrame.MaxFun.exists_maxFun <;> assumption)
