import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatProductFormula
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_elements_bounded_padic : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → ∀ (β : G.Cˣ) (h₂ : Gr G 1), ∃ (B : ℝ) (e : ℕ), ∀ y : grp G β, f' (h₂⁻¹ * toP1 G β y * h₂) ≠ 0 → (∀ (w : Fin G.m) (a b : Fin G.n), ‖((G.rho w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) a b : G.Fw w) : PadicAlgCl p)‖ ≤ B ∧ ‖((G.rho w (sh G (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) a b : G.Fw w) : PadicAlgCl p)‖ ≤ B) ∧ ∃ (k : ℤ) (m : ℕ), ¬ p ∣ m ∧ (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ)⁻¹ * (p : ℚ) ^ e = k / m := by
  first | (exact @GlobalTheory.FixBound.bounded_of_support) | (exact GlobalTheory.FixBound.bounded_of_support) | (intros; apply GlobalTheory.FixBound.bounded_of_support <;> assumption)
