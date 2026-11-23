import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameCoefficientEqOmegaRatio
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramTransformOfCoordinateChangeImports
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExpFourClauses
import Formalism.LocalToGlobal.ProjectiveLattices.OpenRowsFree
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam
open Formalism.DegreeFormula Formalism.MJ GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.FramePairGram

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_coefficient_eq_omega_ratio : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {j : ℕ} (hj : j ≤ r), X.p0 = r - j → ∀ {x x' : Frame X.Ψ r}, x ∈ X.dom → x' ∈ X.dom → ∀ (τ : X.Ψ), moeb (frameCo X hj x τ) 0 = moeb (frameCo X hj x' τ) 0 → (Matrix.of fun b i : Fin (r - j) => coef X x x' (conjEmb τ.1) b i) = (((coOm X hj x τ)⁻¹ * coOm X hj x' τ)ᵀ).submatrix Fin.rev Fin.rev := by
  first | exact @GlobalTheory.FramePairGram.coef_conj_eq_coOm | exact GlobalTheory.FramePairGram.coef_conj_eq_coOm | (intros; apply GlobalTheory.FramePairGram.coef_conj_eq_coOm <;> assumption)
