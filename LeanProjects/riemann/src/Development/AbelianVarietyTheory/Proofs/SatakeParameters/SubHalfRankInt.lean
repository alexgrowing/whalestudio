import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JetOpIntegral
import Formalism.LocalToGlobal.Columns.BaseLemmas

namespace GlobalTheory.ColPeriod

open Formalism.L2.Col Formalism.BasicNotions Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint (WtCompat)

theorem sub_half_rank_int (R : Ranks) (z : ℤ) (j : ℕ) : ∃ a : ℤ, (z : ℚ) - (R.N j : ℚ) / 2 = a := by
  obtain ⟨a, ha⟩ := R.k_even
  obtain ⟨c, hc⟩ := R.t_odd
  unfold Ranks.N
  rw [ha, hc]
  exact ⟨z - a - (j : ℤ) * (c + 1), by push_cast; ring⟩

theorem chainWeights : ChainWeights := by
  intro X Pr R W u j hj
  have hs : ∀ τ : X.Tau, ∃ a : ℤ, sExp R ((W.hc u τ).e ⟨j, hj⟩) (j + 1) = a := by
    intro τ
    obtain ⟨z, hz⟩ := (W.hc u τ).e_int ⟨j, hj⟩
    rw [hz]
    exact sub_half_rank_int R z _
  have hs' : ∀ τ : X.Tau, ∃ a : ℤ, sExp' R ((W.hc u τ).e ⟨j, hj⟩) (j + 1) = a := by
    intro τ
    obtain ⟨z, hz⟩ := (W.hc u τ).e_int ⟨j, hj⟩
    rw [hz]
    exact sub_half_rank_int R z _
  choose s hs using hs
  choose s' hs' using hs'
  have hlt := N_lt_succ R j
  have h1 : ∀ τ (i : Fin (R.N j)),
      (W.lamTrue u (j + 1) τ).w (Fin.castLE hlt.le i) + s τ = (W.lamTrue u j τ).w i + s' τ := by
    intro τ i
    have h := W.lamTrue_old u hj τ (Fin.castLE hlt.le i) i.2
    rw [hs, hs'] at h
    have h' : (((W.lamTrue u (j + 1) τ).w (Fin.castLE hlt.le i) + s τ : ℤ) : ℚ) =
        (((W.lamTrue u j τ).w i + s' τ : ℤ) : ℚ) := by
      push_cast
      rw [h]
      simp
    exact_mod_cast h'
  have h2 : ∀ τ (i : Fin (R.N (j + 1))), R.N j ≤ (i : ℕ) → (W.lamTrue u (j + 1) τ).w i = -s τ := by
    intro τ i hi
    have h := W.lamTrue_new u hj τ i (by omega)
    rw [hs] at h
    exact_mod_cast h
  have h3 : ∀ (τ : X.Tau) (a : Fin (R.N j)), (W.lamTrue u j τ).w a + s' τ = (W.nuW u (j + 1) τ).w a := by
    intro τ a
    have h := W.nuW_eq_true u hj τ a
    rw [hs'] at h
    exact_mod_cast h.symm
  refine ⟨s, s', ⟨h1, h2, fun τ => ?_⟩, h3⟩
  have hpos : 0 < R.N j := R.N_pos j
  have e1 : (W.lamTrue u j τ).detShift = (W.lamTrue u j τ).w ⟨R.N j - 1, by omega⟩ := by
    unfold DomWeight.detShift
    rw [dif_pos hpos]
  have e2 : (W.nuW u (j + 1) τ).detShift = (W.nuW u (j + 1) τ).w (⟨R.N j - 1, by omega⟩ : Fin (R.N j)) := by
    unfold DomWeight.detShift
    exact dif_pos hpos
  have hge : 0 ≤ (W.lamTrue u j τ).w ⟨R.N j - 1, by omega⟩ + s' τ := by
    rw [← h1]
    have ha := (W.lamTrue u (j + 1) τ).anti
      (show Fin.castLE hlt.le (⟨R.N j - 1, by omega⟩ : Fin (R.N j)) ≤ ⟨R.N j, hlt⟩ from by
        rw [Fin.le_def]; simp)
    have hb := h2 τ ⟨R.N j, hlt⟩ le_rfl
    omega
  unfold nuLast
  rw [e1, e2, ← h3, Int.toNat_of_nonneg hge]

end GlobalTheory.ColPeriod
