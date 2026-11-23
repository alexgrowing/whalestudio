import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerFontaineThetaEqSpanOfDistinguished
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
open Ideal WittVector
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ker_fontaineTheta_eq_span_of_distinguished : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (Ideal.span {(p : R)}) R], IsSMulRegular R (p : R) → ∀ ξ : WittVector p (PreTilt R p), fontaineTheta R p ξ = 0 → (∀ c : PreTilt R p, PreTilt.coeff 0 c = 0 → WittVector.constantCoeff ξ ∣ c) → RingHom.ker (fontaineTheta R p) = Ideal.span {ξ} := by
  first | exact @GlobalTheory.ker_fontaineTheta_eq_span_of_dvd | exact GlobalTheory.ker_fontaineTheta_eq_span_of_dvd | (intros; apply GlobalTheory.ker_fontaineTheta_eq_span_of_dvd <;> assumption)
