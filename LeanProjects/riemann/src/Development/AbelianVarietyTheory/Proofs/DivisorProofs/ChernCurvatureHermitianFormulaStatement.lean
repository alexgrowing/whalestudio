import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernCurvatureHermitianFormula
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundConst
open Matrix Filter Topology Set GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianInterpolation GlobalTheory.InterpCurv
open scoped ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chern_curvature_hermitian_formula : ∀ {ι n : Type} [Fintype ι] [Fintype n] [DecidableEq n] {K : (ι → ℂ) → Matrix n n ℂ} {z : ι → ℂ}, MContDiffAt 2 K z → (∀ᶠ x in 𝓝 z, (K x).IsHermitian) → IsUnit (K z).det → ∀ (ξ : ι → ℂ) (v : n → ℂ), form (K z) (curv K z ξ ξ *ᵥ v) v = form (K z) (conn K z ξ *ᵥ v) (conn K z ξ *ᵥ v) - GlobalTheory.ddbar (fun x => form (K x) v v) z ξ ξ := by
  first | exact @GlobalTheory.CurvConstVec.form_curv_const_vec | exact GlobalTheory.CurvConstVec.form_curv_const_vec | (intros; apply GlobalTheory.CurvConstVec.form_curv_const_vec <;> assumption)
