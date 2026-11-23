import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClassSumOfAdicSumUnitSmulTerms
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
open IsLocalRing GlobalTheory.Poinc GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClassSum_of_adicSum_unit_smul_terms : ∀ (O : Type) [CommRing O] (bar : O → O) (q s : ℕ) (W : Matrix (Fin s) (Fin s) ℤ) (A : Type) [CommRing A] [IsLocalRing A] (Φ : VPre bar q W A) (y : Φ.Y) (N : ℕ), 1 ≤ N → ∀ (κ : Fin s → Φ.X y) (c : Φ.Q) (V' : Type) [CommRing V'] [IsLocalRing V'] (io : Φ.V y →+* V') (e : V'ˣ) (x : V'), SumI (maximalIdeal V') (fun nu : Fin s → Φ.X y => (e : V') * io (Φ.term y (κ + N • nu) c)) x → Φ.IsClassSum y N κ c io (((e⁻¹ : V'ˣ) : V') * x) := by
  first | exact @GlobalTheory.Poinc.isClassSum_of_sumI | exact GlobalTheory.Poinc.isClassSum_of_sumI | (intros; apply GlobalTheory.Poinc.isClassSum_of_sumI <;> assumption)
