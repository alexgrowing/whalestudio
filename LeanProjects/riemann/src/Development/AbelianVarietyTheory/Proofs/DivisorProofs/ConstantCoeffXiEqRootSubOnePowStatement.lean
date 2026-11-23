import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffXiEqRootSubOnePow
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
open Ideal WittVector
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constantCoeff_xi_eq_root_sub_one_pow : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (ε : PreTilt O p), WittVector.constantCoeff (GlobalTheory.Sandwich.xi ε) = (GlobalTheory.Sandwich.root ε - 1) ^ (p - 1) := by
  first | exact @GlobalTheory.Sandwich.constantCoeff_xi | exact GlobalTheory.Sandwich.constantCoeff_xi | (intros; apply GlobalTheory.Sandwich.constantCoeff_xi <;> assumption)
