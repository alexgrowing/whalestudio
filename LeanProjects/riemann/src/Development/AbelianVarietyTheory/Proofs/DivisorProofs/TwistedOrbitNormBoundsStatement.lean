import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitNormBounds
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_orbit_norm_bounds : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ), 0 < r → IsTest (sigG G r) (KHT p G.m G.n r G.Fw) K φ → ∃ k : ℕ, ∀ (γ : Gp G) (δ z y : Gr G r), IsNrm G r γ δ z → φ (y⁻¹ * δ * sigG G r y) ≠ 0 → ‖((γ.1 : ℚ_[p]ˣ) : ℚ_[p])‖ ≤ (p : ℝ) ^ k ∧ ‖((γ.1⁻¹ : ℚ_[p]ˣ) : ℚ_[p])‖ ≤ (p : ℝ) ^ k ∧ (∀ (w : Fin G.m) (μ : PadicAlgCl p), (((γ.2 w : GL (Fin G.n) (G.Fw w)) : Matrix (Fin G.n) (Fin G.n) (G.Fw w)).charpoly.map (algebraMap (G.Fw w) (PadicAlgCl p))).IsRoot μ → ‖μ‖ ≤ (p : ℝ) ^ k) ∧ (∀ (w : Fin G.m) (μ : PadicAlgCl p), ((((γ.2 w)⁻¹ : GL (Fin G.n) (G.Fw w)) : Matrix (Fin G.n) (Fin G.n) (G.Fw w)).charpoly.map (algebraMap (G.Fw w) (PadicAlgCl p))).IsRoot μ → ‖μ‖ ≤ (p : ℝ) ^ k) := by
  first | (exact @GlobalTheory.AtPBd.main) | (exact GlobalTheory.AtPBd.main) | (intros; apply GlobalTheory.AtPBd.main  <;> assumption)
