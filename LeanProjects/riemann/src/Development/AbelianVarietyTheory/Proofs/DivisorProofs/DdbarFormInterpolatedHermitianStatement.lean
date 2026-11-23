import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DdbarFormInterpolatedHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundConst
open Matrix Filter Topology Set GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianInterpolation GlobalTheory.InterpCurv
open scoped ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ddbar_form_interpolated_hermitian : ∀ {ι n : Type} [Fintype ι] [Fintype n] [DecidableEq n] {H₀ H : (ι → ℂ) → Matrix n n ℂ} {s : (ι → ℂ) → ℝ} {z : ι → ℂ}, MContDiffAt 2 H₀ z → MContDiffAt 2 H z → ContDiffAt ℝ 2 s z → (∀ᶠ x in 𝓝 z, (H₀ x).IsHermitian) → (∀ᶠ x in 𝓝 z, (H x).IsHermitian) → IsUnit (H₀ z).det → IsUnit (H z).det → ∀ (ξ : ι → ℂ) (v : n → ℂ), GlobalTheory.ddbar (fun x => form (interp H₀ H s x) v v) z ξ ξ = ((1 - s z : ℝ) : ℂ) * GlobalTheory.ddbar (fun x => form (H₀ x) v v) z ξ ξ + (s z : ℂ) * GlobalTheory.ddbar (fun x => form (H x) v v) z ξ ξ + (form (H z) v v - form (H₀ z) v v) * GlobalTheory.leviForm s z ξ ξ + GlobalTheory.del (fun x => (s x : ℂ)) z ξ * (form (H z) v (conn H z ξ *ᵥ v) - form (H₀ z) v (conn H₀ z ξ *ᵥ v)) + starRingEnd ℂ (GlobalTheory.del (fun x => (s x : ℂ)) z ξ) * (form (H z) (conn H z ξ *ᵥ v) v - form (H₀ z) (conn H₀ z ξ *ᵥ v) v) := by
  first | exact @GlobalTheory.InterpCurv.ddbar_form_interp | exact GlobalTheory.InterpCurv.ddbar_form_interp | (intros; apply GlobalTheory.InterpCurv.ddbar_form_interp <;> assumption)
