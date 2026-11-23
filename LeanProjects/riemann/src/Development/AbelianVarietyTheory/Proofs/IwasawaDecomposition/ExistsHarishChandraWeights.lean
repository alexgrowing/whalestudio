import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DuStarPos
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SpreadLe
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AssembleLattice
import Formalism.SharpRestriction.InertJacobiLevels.HostFam
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HarishChandraParameterFormulaStatement

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem

namespace GlobalTheory.Mem

theorem exists_preCh_of_prescribed : ∀ (R : Ranks) (H : Host R) (u0 : R.A), H.ccK = ⊤ → (∀ p ∈ H.levelPrimes, p.Prime ∧ p % (H.QS * H.q * H.d) = 1) → Disjoint (Formalism.CyclotomicNorms.BB R.r (H.g 0)) (Formalism.CyclotomicNorms.BB R.r (H.g 1)) → ∀ (M : ℕ), 0 < M → ∀ (c : Fin M → Fin (R.k - 2) → Bool) (Del hh : ℕ) (uF uL b1 : Tau R → ℤ), 1 ≤ Del → R.t + 3 ≤ 2 * hh → (∀ τ, ((R.k - 2 : ℕ) : ℤ) * (4 * Del) ≤ uF τ ∧ uL τ ≤ -1 ∧ -b1 τ ≤ uL τ) → ∃ hcW : Fin M → Tau R → HCParam R, (∀ u τ, (∀ i : Fin (R.k - 1), (hcW u τ).v i = ((R.k - 2 - i.1 : ℕ) : ℚ) * (4 * (Del : ℚ))) ∧ (∀ j : Fin R.m, (hcW u τ).b j = (b1 τ : ℚ) + (j.1 : ℚ) * (2 * hh : ℚ) ∧ (hcW u τ).e j = (hcW u τ).b j + hh) ∧ (∀ h : 0 < R.k, (hcW u τ).u ⟨0, h⟩ = (uF τ : ℚ) + 1 / 2 ∧ (hcW u τ).u ⟨R.k - 1, by omega⟩ = (uL τ : ℚ) + 1 / 2) ∧ ∀ (l : ℕ) (h : l < R.k - 2), (hcW u τ).u ⟨l + 1, by omega⟩ = (hcW u τ).v ⟨l, by omega⟩ - 1 / 2 - (if c u ⟨l, h⟩ then (Del : ℚ) else 0)) ∧ ∃ P : PreCh, P.R = R ∧ HEq P.H ({ H with u0 := u0 } : Host R) ∧ P.Word = Fin M ∧ HEq P.hcW hcW := by
  intro R H u0 hcc hlev hBB M hM c Del hh uF uL b1 hDel hhh hends
  choose hcW hW using fun (u : Fin M) (τ : Tau R) =>
    GlobalTheory.T.harish_chandra_parameter_formula R Del hh (uF τ) (uL τ) (b1 τ) hDel hhh (hends τ).1 (hends τ).2.1 (hends τ).2.2 (c u)
  refine ⟨hcW, hW, ?_⟩
  have hb : ∀ u u' τ, (hcW u τ).b = (hcW u' τ).b := fun u u' τ => funext fun j => by
    rw [((hW u τ).2.1 j).1, ((hW u' τ).2.1 j).1]
  refine ⟨{ R := R
            H := { H with u0 := u0 }
            ccK_top := hcc
            level_cond := hlev
            BB_disj := hBB
            Word := Fin M
            u₀ := ⟨0, hM⟩
            hcW := hcW
            hcW_v := fun u τ => funext fun i => by rw [(hW u τ).1 i, (hW _ τ).1 i]
            hcW_b := fun u τ => hb _ _ τ
            hcW_e := fun u τ => funext fun j => by
              rw [((hW u τ).2.1 j).2, ((hW _ τ).2.1 j).2, hb u ⟨0, hM⟩ τ]
            hcW_first := fun u τ h => by rw [((hW u τ).2.2.1 h).1, ((hW _ τ).2.2.1 h).1]
            hcW_last := fun u τ h => by rw [((hW u τ).2.2.1 h).2, ((hW _ τ).2.2.1 h).2] },
    rfl, HEq.rfl, rfl, HEq.rfl⟩

end GlobalTheory.Mem
