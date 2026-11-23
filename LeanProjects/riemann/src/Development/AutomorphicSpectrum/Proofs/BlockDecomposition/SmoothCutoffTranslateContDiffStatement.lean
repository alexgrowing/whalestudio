import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothCutoffTranslateContDiff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LastRowMulRowGLInv
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter GlobalTheory.CuspGeneric GlobalTheory.CuspRep PositivityTheory.jumpWindows PositivityTheory.AdelicQuotientData GroundTheory.Automorphic.FourierWhittaker GlobalTheory.CompanionTheory.CutOff
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_cutoff_translate_contDiff : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {k : ℕ} {φ : XB E k}, SmV (repI E k) φ → ∀ {b : (Fin k → Cinf E) → ℝ}, ContDiff ℝ ∞ b → (∀ x ∈ tsupport b, IsUnit (lastEnt x)) → ContDiff ℝ ∞ fun x => (b x : ℂ) • Rt E k (infGL E k (rowGL x))⁻¹ φ := by
  first | exact @GlobalTheory.CompanionTheory.CutOff.contDiff_cut_orbit | exact GlobalTheory.CompanionTheory.CutOff.contDiff_cut_orbit | (intros; apply GlobalTheory.CompanionTheory.CutOff.contDiff_cut_orbit <;> assumption)
