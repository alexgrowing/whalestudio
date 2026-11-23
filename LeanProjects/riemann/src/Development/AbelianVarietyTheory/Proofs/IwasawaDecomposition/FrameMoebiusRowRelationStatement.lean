import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameMoebiusRowRelation
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalCompactificationData
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam
open Formalism.DegreeFormula Formalism.MJ GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open scoped ComplexOrder ContDiff
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_moebius_row_relation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (j : ℕ) (hj : j ≤ r), X.p0 = r - j → ∀ (x : Frame X.Ψ r), x ∈ X.dom → ∀ ψ : X.Ψ, ∃ R : Matrix (Fin j) (Fin j ⊕ Fin (r - j)) ℂ, R * Matrix.fromRows (moeb (frameCo X hj x ψ) 0) (1 : Matrix (Fin (r - j)) (Fin (r - j)) ℂ) = 0 ∧ (∃ Rr : Matrix (Fin j ⊕ Fin (r - j)) (Fin j) ℂ, R * Rr = 1) ∧ ∀ (v : Fin r → ℂ) (i : Fin j) (hi : X.p0 + (i : ℕ) < r), ((mat x ψ)⁻¹.mulVec v) ⟨X.p0 + i, hi⟩ = (R.mulVec fun m => ((mat (x0F X) ψ)⁻¹.mulVec v) ((idx hj).symm m)) i := by
  first | exact @GlobalTheory.ShFam.frameCo_inv_rows | exact GlobalTheory.ShFam.frameCo_inv_rows | (intros; apply GlobalTheory.ShFam.frameCo_inv_rows <;> assumption)
