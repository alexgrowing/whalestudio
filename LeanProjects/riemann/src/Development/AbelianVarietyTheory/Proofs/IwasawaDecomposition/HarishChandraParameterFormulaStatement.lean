import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HarishChandraParameterFormula
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DuStarPos
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SpreadLe
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AssembleLattice
import Formalism.SharpRestriction.InertJacobiLevels.HostFam
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harish_chandra_parameter_formula : ∀ (R : Ranks) (Del hh : ℕ) (uF uL b1 : ℤ), 1 ≤ Del → R.t + 3 ≤ 2 * hh → ((R.k - 2 : ℕ) : ℤ) * (4 * Del) ≤ uF → uL ≤ -1 → -b1 ≤ uL → ∀ c : Fin (R.k - 2) → Bool, ∃ P : HCParam R, (∀ i : Fin (R.k - 1), (P).v i = ((R.k - 2 - i.1 : ℕ) : ℚ) * (4 * (Del : ℚ))) ∧ (∀ j : Fin R.m, (P).b j = (b1 : ℚ) + (j.1 : ℚ) * (2 * hh : ℚ) ∧ (P).e j = (P).b j + hh) ∧ (∀ h : 0 < R.k, (P).u ⟨0, h⟩ = (uF : ℚ) + 1 / 2 ∧ (P).u ⟨R.k - 1, by omega⟩ = (uL : ℚ) + 1 / 2) ∧ ∀ (l : ℕ) (h : l < R.k - 2), (P).u ⟨l + 1, by omega⟩ = (P).v ⟨l, by omega⟩ - 1 / 2 - (if c ⟨l, h⟩ then (Del : ℚ) else 0) := by
  first | exact @GlobalTheory.Mem.exists_hcParam_std | exact GlobalTheory.Mem.exists_hcParam_std | (intros; apply GlobalTheory.Mem.exists_hcParam_std <;> assumption)
