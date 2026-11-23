import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeSumPolynomialBound
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MajINonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_sum_polynomial_bound : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [DecidableEq κ] (q : ℕ) (blk : Fin q → Finset κ)
    (A N₀ : ℕ) (c : ℝ), 0 < c → ∃ (N : ℕ) (C : ℝ) (K : ℕ), ∀ (m : ℕ) (t : Fin q → ℝ), 1 ≤ m → (∀ i, c ≤ t i) →
      Summable (latG (F := F) blk A N m t) ∧ (∑' ξ, latG (F := F) blk A N m t ξ) * (1 + ∏ i, t i) ^ N₀ ≤ C * (m : ℝ) ^ K := by
  first | exact @GlobalTheory.ThKTorusLatSum.latG_tsum_le | exact GlobalTheory.ThKTorusLatSum.latG_tsum_le | (intros; apply GlobalTheory.ThKTorusLatSum.latG_tsum_le <;> assumption)
