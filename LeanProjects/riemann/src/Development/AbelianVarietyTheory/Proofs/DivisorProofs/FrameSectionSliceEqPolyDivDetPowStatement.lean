import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameSectionSliceEqPolyDivDetPow
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import ReciprocityTheory.SemistableReduction.LatAll
open NumberField ReciprocityTheory.ChartRestriction.G.FD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameSection_slice_eq_poly_div_det_pow : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) [DecidableEq X.Ψ], (∀ x : Frame X.Ψ r, x ∈ X.dom ↔ ∀ τ, (mat x τ).det ≠ 0) → ∀ (la : Wt X.Ψ r) (N : ℕ), (∀ τ i, 0 ≤ la τ i + N) → ∀ P : Frame X.Ψ r → ℂ, X.IsSec la P → ∀ x ∈ X.dom, ∀ τ : X.Ψ, ∃ F : MvPolynomial (Fin r × Fin r) ℂ, F.IsHomogeneous (∑ i, (la τ i + N).toNat) ∧ ∀ y : Fin r → Fin r → ℂ, (Matrix.of y).det ≠ 0 → P (Function.update x τ y) = MvPolynomial.eval (fun ij => y ij.1 ij.2) F * ((Matrix.of y).det)⁻¹ ^ N := by
  first | exact @GlobalTheory.section_slice_eq_poly_div_det_pow | exact GlobalTheory.section_slice_eq_poly_div_det_pow | (intros; apply GlobalTheory.section_slice_eq_poly_div_det_pow <;> assumption)
