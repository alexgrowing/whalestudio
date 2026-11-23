import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoxFourierIntegralBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LastRowMulRowGLInv
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter GlobalTheory.CuspGeneric GlobalTheory.CuspRep PositivityTheory.jumpWindows PositivityTheory.AdelicQuotientData GroundTheory.Automorphic.FourierWhittaker GlobalTheory.CompanionTheory.CutOff
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.box_fourier_integral_bound : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {k : ℕ} {ψ : AddChar (Ad E) ℂ}, (∀ x, ‖ψ x‖ = 1) → Continuous ψ → ∀ (L : AddSubgroup (Af E)), IsCompact (L : Set (Af E)) → IsOpen (L : Set (Af E)) → ∀ (c z : Fin k → Af E), ‖∫ f, (((boxL (L : Set (Af E)) c).indicator (fun _ => (1 : ℝ)) f : ℝ) : ℂ) * ψ (sFin E (∑ i, f i * z i)) ∂nuFin E k‖ ≤ (nuFin E k).real (boxL (L : Set (Af E)) c) ∧ (∫ f, (((boxL (L : Set (Af E)) c).indicator (fun _ => (1 : ℝ)) f : ℝ) : ℂ) * ψ (sFin E (∑ i, f i * z i)) ∂nuFin E k ≠ 0 → ∀ i, ∀ a ∈ L, ψ (sFin E (a * z i)) = 1) := by
  first | exact @GlobalTheory.CompanionTheory.CutOff.FinFT.box_fourier_main | exact GlobalTheory.CompanionTheory.CutOff.FinFT.box_fourier_main | (intros; apply GlobalTheory.CompanionTheory.CutOff.FinFT.box_fourier_main <;> assumption)
