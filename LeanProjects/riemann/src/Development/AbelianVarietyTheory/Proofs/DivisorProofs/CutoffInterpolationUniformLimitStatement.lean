import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CutoffInterpolationUniformLimit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundConst
open Matrix Filter Topology Set GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianInterpolation GlobalTheory.InterpCurv
open scoped ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cutoff_interpolation_uniform_limit : ∀ {ι n : Type} [Fintype ι] [Fintype n] [DecidableEq n] {Cμ κ : ℝ} {χ : ℝ → ℝ}, IsCutoff χ → 2 * Cμ + 2 < κ → ∀ {U : Set (ι → ℂ)} {H₀ H : (ι → ℂ) → Matrix n n ℂ} {r : (ι → ℂ) → ℝ}, IsPosFrame U H₀ → IsPosFrame U H → ContDiffOn ℝ ∞ r U → (∀ z ∈ U, Real.exp 1 ≤ r z) → PowComparable U r Cμ H₀ H → ∀ K : Set (ι → ℂ), IsCompact K → K ⊆ U → ∀ (k : ℕ) (a b : n), TendstoUniformlyOn (fun (R : ℝ) z => iteratedFDeriv ℝ k (fun x => interp H₀ H (cutWeight χ κ R r) x a b) z) (iteratedFDeriv ℝ k fun x => H x a b) atTop K := by
  first | exact @GlobalTheory.InterpLimit.tendstoUniformlyOn_iteratedFDeriv_interp | exact GlobalTheory.InterpLimit.tendstoUniformlyOn_iteratedFDeriv_interp | (intros; apply GlobalTheory.InterpLimit.tendstoUniformlyOn_iteratedFDeriv_interp <;> assumption)
