import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TiltUntiltDividesPow
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
open Ideal WittVector
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tilt_untilt_divides_pow : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (Ideal.span {(p : R)}) R], IsSMulRegular R (p : R) → ∀ (pflat f : PreTilt R p), PreTilt.untilt pflat = (p : R) → (∀ c : PreTilt R p, PreTilt.coeff 0 c = 0 → pflat ∣ c) → Associated ((PreTilt.untilt f - 1) ^ (p * (p - 1))) (p : R) → ∀ c : PreTilt R p, PreTilt.coeff 0 c = 0 → (f ^ p - 1) ^ (p - 1) ∣ c := by
  first | exact @GlobalTheory.preTilt_pow_sub_one_pow_dvd_of_associated | exact GlobalTheory.preTilt_pow_sub_one_pow_dvd_of_associated | (intros; apply GlobalTheory.preTilt_pow_sub_one_pow_dvd_of_associated <;> assumption)
