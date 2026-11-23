import Mathlib
import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ShiftExists
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WignerMapsThreePlacesExistsStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsShiftedTypesLowerBound
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WithRightAction

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.CutBP2

namespace GlobalTheory.wignerShiftedPlacesExist_proof

theorem gap_one {P : M.Par} (h : P.OK) (i : ℕ) (hi : i ∈ Finset.Icc 1 (P.k - 1)) :
    P.u' (i + 1) + 1 ≤ P.u' i := by
  have hg := h.gap i hi
  unfold M.Par.lo M.Par.hi at hg
  have h1 := le_max_right (P.u (i + 1)) (P.u' (i + 1))
  have h2 := min_le_right (P.u i) (P.u' i)
  linarith

theorem gap_nat {P : M.Par} (h : P.OK) (i : ℕ) (hi : i ∈ Finset.Icc 1 (P.k - 1)) :
    ∃ N : ℕ, P.u' i - P.u' (i + 1) = (N : ℝ) + 1 := by
  have h1 := gap_one h i hi
  rw [Finset.mem_Icc] at hi
  obtain ⟨a, ha⟩ := h.int_u' i (Finset.mem_Icc.2 ⟨hi.1, by omega⟩)
  obtain ⟨c, hc⟩ := h.int_u' (i + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
  have h2 : ((0 : ℤ) : ℝ) ≤ ((a - c - 1 : ℤ) : ℝ) := by push_cast; linarith
  have h3 : (0 : ℤ) ≤ a - c - 1 := by exact_mod_cast h2
  refine ⟨(a - c - 1).toNat, ?_⟩
  have h4 : (((a - c - 1).toNat : ℤ) : ℝ) = ((a - c - 1 : ℤ) : ℝ) := by rw [Int.toNat_of_nonneg h3]
  push_cast at h4
  linarith

theorem ok_plus {P : M.Par} (h : P.OK) (l n₀ : ℕ) (he : ∀ i ∈ Finset.Icc 1 P.k, P.u i = P.u' i)
    (hg : 2 * (n₀ : ℝ) + 1 ≤ P.u' l - P.u' (l + 1)) :
    (shP P P.u (Function.update P.u' (l + 1) (P.u' (l + 1) + (n₀ : ℝ)))).OK := by
  have hn : (0 : ℝ) ≤ n₀ := Nat.cast_nonneg _
  refine ⟨h.k_pos, h.T_pos, h.T'_pos, h.int_u, ?_, ?_⟩
  · intro i hi
    obtain ⟨a, ha⟩ := h.int_u' i hi
    change ∃ n : ℤ, Function.update P.u' (l + 1) (P.u' (l + 1) + (n₀ : ℝ)) i - P.u 1 = n
    by_cases hil : i = l + 1
    · subst hil
      refine ⟨a + n₀, ?_⟩
      rw [Function.update_self]; push_cast; linarith
    · exact ⟨a, by rw [Function.update_of_ne hil]; exact ha⟩
  · intro i hi
    have h1 := gap_one h i hi
    change i ∈ Finset.Icc 1 (P.k - 1) at hi
    rw [Finset.mem_Icc] at hi
    have e1 := he i (Finset.mem_Icc.2 ⟨hi.1, by omega⟩)
    have e2 := he (i + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
    change max (P.u (i + 1)) (Function.update P.u' (l + 1) (P.u' (l + 1) + (n₀ : ℝ)) (i + 1)) + 1 / 2 ≤
      min (P.u i) (Function.update P.u' (l + 1) (P.u' (l + 1) + (n₀ : ℝ)) i) - 1 / 2
    rw [e1, e2]
    by_cases ha : i = l
    · subst ha
      rw [Function.update_self, Function.update_of_ne (by omega), min_self, max_eq_right (by linarith)]
      linarith
    · rw [Function.update_of_ne (show i + 1 ≠ l + 1 by omega), max_self]
      by_cases hb : i = l + 1
      · subst hb
        rw [Function.update_self, min_eq_left (by linarith)]
        linarith
      · rw [Function.update_of_ne hb, min_self]
        linarith

theorem ok_minus {P : M.Par} (h : P.OK) (l n₀ : ℕ) (he : ∀ i ∈ Finset.Icc 1 P.k, P.u i = P.u' i)
    (hg : 2 * (n₀ : ℝ) + 1 ≤ P.u' l - P.u' (l + 1)) :
    (shP P P.u (Function.update P.u' l (P.u' l - (n₀ : ℝ)))).OK := by
  have hn : (0 : ℝ) ≤ n₀ := Nat.cast_nonneg _
  refine ⟨h.k_pos, h.T_pos, h.T'_pos, h.int_u, ?_, ?_⟩
  · intro i hi
    obtain ⟨a, ha⟩ := h.int_u' i hi
    change ∃ n : ℤ, Function.update P.u' l (P.u' l - (n₀ : ℝ)) i - P.u 1 = n
    by_cases hil : i = l
    · subst hil
      refine ⟨a - n₀, ?_⟩
      rw [Function.update_self]; push_cast; linarith
    · exact ⟨a, by rw [Function.update_of_ne hil]; exact ha⟩
  · intro i hi
    have h1 := gap_one h i hi
    change i ∈ Finset.Icc 1 (P.k - 1) at hi
    rw [Finset.mem_Icc] at hi
    have e1 := he i (Finset.mem_Icc.2 ⟨hi.1, by omega⟩)
    have e2 := he (i + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
    change max (P.u (i + 1)) (Function.update P.u' l (P.u' l - (n₀ : ℝ)) (i + 1)) + 1 / 2 ≤
      min (P.u i) (Function.update P.u' l (P.u' l - (n₀ : ℝ)) i) - 1 / 2
    rw [e1, e2]
    by_cases ha : i = l
    · subst ha
      rw [Function.update_self, Function.update_of_ne (by omega), max_self, min_eq_right (by linarith)]
      linarith
    · rw [Function.update_of_ne ha, min_self]
      by_cases hb : i + 1 = l
      · subst hb
        rw [Function.update_self, max_eq_left (by linarith)]
        linarith
      · rw [Function.update_of_ne hb, max_self]
        linarith

theorem shiftExists_of (hA : GlobalTheory.WigSh.AmapsShExists) : GlobalTheory.WigSh.ShiftExists := by
  obtain ⟨c₃, hc⟩ := hA
  obtain ⟨Cb, hCb, hS⟩ := GlobalTheory.WithRightAction.exists_place_other_right_type
  refine ⟨c₃, Cb, hCb, ?_⟩
  intro P Wp Wq _ _ _ _ _ _ p l n₀ lp lm b he hl1 hl2 hg hb hn hb1 hp1 hp2 hm1 hm2
  obtain ⟨hOK, hz, hz', hT, hT', hπ, hπ'⟩ := p.hP
  obtain ⟨Wqp, i1, i2, i3, Wqm, j1, j2, j3, πp, πm, -, -, htp, htm, -⟩ :=
    GlobalTheory.WigSh.exists_shifted_types_lower_bound Wq P.k P.r p.T.base.z' p.T.base.π' P.u' l n₀ b hz'
      (by rw [hT']; exact hOK.T'_pos) hπ' (gap_nat hOK) hl1 hl2 hg hb hn hb1
  obtain ⟨pp, a1, a2, a3, a4, -, a6, a7, a8⟩ := hS P Wp Wq Wqp p P.u
    (Function.update P.u' (l + 1) (P.u' (l + 1) + (n₀ : ℝ))) πp lp
    ⟨ok_plus hOK l n₀ he hg, hz, hz', hT, hT', hπ, htp⟩ hp1 hp2
  obtain ⟨pm, b1, b2, b3, b4, -, b6, b7, b8⟩ := hS P Wp Wq Wqm p P.u
    (Function.update P.u' l (P.u' l - (n₀ : ℝ))) πm lm
    ⟨ok_minus hOK l n₀ he hg, hz, hz', hT, hT', hπ, htm⟩ hm1 hm2
  obtain ⟨Ap, Am, ApPt, AmPt, c1, c2, c3, c4⟩ := hc P Wp Wq Wqp Wqm P.u
    (Function.update P.u' (l + 1) (P.u' (l + 1) + (n₀ : ℝ))) P.u (Function.update P.u' l (P.u' l - (n₀ : ℝ)))
    p pp pm l n₀ b a2 a3 b2 b3 (fun h _ => congrFun a4 h) (fun h _ => congrFun b4 h) a6 a7 b6 b7 hl1 hl2 hg hb hn hb1
    (fun i _ => by
      by_cases h : i = l + 1
      · subst h; simp
      · rw [Function.update_of_ne h, if_neg h])
    (fun i _ => by
      by_cases h : i = l
      · subst h; simp
      · rw [Function.update_of_ne h, if_neg h])
  exact ⟨Wqp, i1, i2, i3, Wqm, j1, j2, j3, pp, pm, Ap, Am, ApPt, AmPt, a1, b1, a2, a3, a4, b2, b3, b4, a8, b8,
    c1, c2, c3, c4⟩

theorem shiftExists : GlobalTheory.WigSh.ShiftExists := shiftExists_of GlobalTheory.T.wignerMapsThreePlaces_exists

end GlobalTheory.wignerShiftedPlacesExist_proof
