import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarmonicSectionLaplacian
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarEqZeroOfHolomorphic
open Matrix GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.FlatAcyc
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harmonic_section_laplacian : ∀ {g : ℕ} (G K : Matrix (Fin g) (Fin g) ℂ) (hKG : Kᵀ * G = 2)
    (ψ : (Fin g → ℂ) → ℂ) (hψ : ContDiff ℝ 2 ψ)
    (hdd : ∀ z a c, d10 (fun z' => d01 ψ z' (ev c)) z (ev a) = -(π : ℂ) * K a c)
    (f : (Fin g → ℂ) → Ext (0 + 0 + g)) (hf : ContDiff ℝ 2 f) (hharm : ∀ z, fibreOp G ψ f z = 0)
    (z : Fin g → ℂ) (S : Finset (Fin (0 + 0 + g))),
    ∑ a, ∑ c, G a c * (d10 (fun z' => d01 (fun z'' => f z'' S) z' (ev c)) z (ev a) +
      d10 ψ z (ev a) * d01 (fun z'' => f z'' S) z (ev c)) = 2 * π * S.card * f z S := by
  first | exact @GlobalTheory.TorsionForm.FlatAcyc.harmonic_weitzenboeck | exact GlobalTheory.TorsionForm.FlatAcyc.harmonic_weitzenboeck | (intros; apply GlobalTheory.TorsionForm.FlatAcyc.harmonic_weitzenboeck <;> assumption)
