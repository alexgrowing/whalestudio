import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedEigenvaluesClasses
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bounded_eigenvalues_classes : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), IsSimple G → ∀ (β y : G.Cˣ) (c : ℚˣ), (y : G.C) * β * sh G y = algebraMap ℚ G.C c * β → ∀ B : ℝ, ‖((c : ℚ) : ℚ_[p])‖ ≤ B → ‖(((c⁻¹ : ℚˣ) : ℚ) : ℚ_[p])‖ ≤ B → (∀ (w : Fin G.m) (μ : PadicAlgCl p), ((G.rho w (y : G.C)).charpoly.map (algebraMap (G.Fw w) (PadicAlgCl p))).IsRoot μ → ‖μ‖ ≤ B) → (∀ (w : Fin G.m) (μ : PadicAlgCl p), ((G.rho w ((y⁻¹ : G.Cˣ) : G.C)).charpoly.map (algebraMap (G.Fw w) (PadicAlgCl p))).IsRoot μ → ‖μ‖ ≤ B) → ∀ μ : PadicAlgCl p, ((LinearMap.mulLeft ℚ (y : G.C)).charpoly.map (algebraMap ℚ (PadicAlgCl p))).IsRoot μ → ‖μ‖ ≤ B * B := by
  first | (exact @GlobalTheory.GlobEig.root_norm_le) | (exact GlobalTheory.GlobEig.root_norm_le) | (intros; apply GlobalTheory.GlobEig.root_norm_le  <;> assumption)
