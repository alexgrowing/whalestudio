import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHarishChandraWeights
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DuStarPos
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SpreadLe
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AssembleLattice
import Formalism.SharpRestriction.InertJacobiLevels.HostFam
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_harish_chandra_weights : ∀ (R : Ranks) (H : Host R) (u0 : R.A), H.ccK = ⊤ → (∀ p ∈ H.levelPrimes, p.Prime ∧ p % (H.QS * H.q * H.d) = 1) → Disjoint (Formalism.CyclotomicNorms.BB R.r (H.g 0)) (Formalism.CyclotomicNorms.BB R.r (H.g 1)) → ∀ (M : ℕ), 0 < M → ∀ (c : Fin M → Fin (R.k - 2) → Bool) (Del hh : ℕ) (uF uL b1 : Tau R → ℤ), 1 ≤ Del → R.t + 3 ≤ 2 * hh → (∀ τ, ((R.k - 2 : ℕ) : ℤ) * (4 * Del) ≤ uF τ ∧ uL τ ≤ -1 ∧ -b1 τ ≤ uL τ) → ∃ hcW : Fin M → Tau R → HCParam R, (∀ u τ, (∀ i : Fin (R.k - 1), (hcW u τ).v i = ((R.k - 2 - i.1 : ℕ) : ℚ) * (4 * (Del : ℚ))) ∧ (∀ j : Fin R.m, (hcW u τ).b j = (b1 τ : ℚ) + (j.1 : ℚ) * (2 * hh : ℚ) ∧ (hcW u τ).e j = (hcW u τ).b j + hh) ∧ (∀ h : 0 < R.k, (hcW u τ).u ⟨0, h⟩ = (uF τ : ℚ) + 1 / 2 ∧ (hcW u τ).u ⟨R.k - 1, by omega⟩ = (uL τ : ℚ) + 1 / 2) ∧ ∀ (l : ℕ) (h : l < R.k - 2), (hcW u τ).u ⟨l + 1, by omega⟩ = (hcW u τ).v ⟨l, by omega⟩ - 1 / 2 - (if c u ⟨l, h⟩ then (Del : ℚ) else 0)) ∧ ∃ P : PreCh, P.R = R ∧ HEq P.H ({ H with u0 := u0 } : Host R) ∧ P.Word = Fin M ∧ HEq P.hcW hcW := by
  first | exact @GlobalTheory.Mem.exists_preCh_of_prescribed | exact GlobalTheory.Mem.exists_preCh_of_prescribed | (intros; apply GlobalTheory.Mem.exists_preCh_of_prescribed <;> assumption)
