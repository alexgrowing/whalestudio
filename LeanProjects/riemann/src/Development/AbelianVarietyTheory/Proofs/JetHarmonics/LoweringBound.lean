import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NumericalFamilyShapeGapsStatement
import Formalism.FlagUnipotentLattices.AlgebraicIdentityHigherDegree

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.PieriBound

theorem bound_cast (k M n : ℕ) (hn : n = k + M) (lam mu : Fin n → ℝ) (u : ℕ → ℝ) (b bv ga q0 : ℝ) (s : Fin n)
    (hk : 1 ≤ k) (hM : 1 ≤ M) (h1 : StrictAnti lam) (h2 : ∀ a c, ∃ z : ℤ, lam a - lam c = (z : ℝ))
    (h3 : ∀ a, ∀ i ∈ Icc 1 k, ∃ m : ℤ, lam a - u i = (m : ℝ) + 1 / 2)
    (h4 : ∀ a : Fin n, a.val < k → lam a < u (a.val + 1))
    (h5 : ∀ a : Fin n, a.val + 1 < k → u (a.val + 2) < lam a)
    (h6 : ∀ a : Fin n, a.val + 1 < k → 0 ≤ lam a ∧ lam a ≤ bv / 8)
    (h7 : ∀ a : Fin n, k ≤ a.val + 1 → -2 * bv ≤ lam a ∧ lam a ≤ -bv)
    (h8 : ∀ a, |lam a| ≤ b) (h9 : ∀ i ∈ Icc 1 k, |u i| ≤ b)
    (h10 : ∀ a c : Fin n, a < c → c.val + 1 < k → ga ≤ lam a - lam c) (h11 : 4 ≤ ga)
    (h12 : ∀ a, ∃ z : ℤ, mu a - lam a = (z : ℝ)) (h13 : StrictAnti mu)
    (h14 : ∑ a, |mu a - lam a| ≤ q0) (h15 : q0 ≤ ga / 8) (h16 : q0 ≤ bv / 4) (h17 : q0 ≤ b)
    (h18 : ∀ s', s' ≠ s → mu s - 1 ≠ mu s') :
    (∏ i ∈ Icc 1 k, |mu s - 1 / 2 - u i|) / ∏ s' ∈ univ.erase s, |mu s - 1 - mu s'| ≤
      if (s : ℕ) + 1 < k then 64 * Real.exp 1 * Real.sqrt k * b ^ 3 else 16 * Real.exp 1 * b ^ 2 := by
  subst hn
  have hmem : ∀ i : Fin k, (i : ℕ) + 1 ∈ Icc 1 k := fun i => by
    rw [Finset.mem_Icc]; have := i.2; omega
  have key := Formalism.HermitianLatticeCounting.Final.ExpansionTerms.sup_l2_ratio_majorant k M lam mu (fun i => u (i.val + 1)) b bv ga q0 s hk hM
    ⟨h1, h2, fun a i => h3 a _ (hmem i), fun i => h4 (Fin.castAdd M i) i.2,
      fun i j hij => by
        have := h5 (Fin.castAdd M i) (by have := j.2; simp only [Fin.val_castAdd]; omega)
        simp only [Fin.val_castAdd] at this
        show u (j.val + 1) < _
        rw [← hij]; exact this,
      h6, h7, h8, fun i => h9 _ (hmem i), h10, h11, h12, h13, h14, h15, h16, h17⟩ h18
  have e : (∏ i ∈ Icc 1 k, |mu s - 1 / 2 - u i|) = ∏ i : Fin k, |mu s - 1 / 2 - u (i.val + 1)| := by
    rw [Fin.prod_univ_eq_prod_range (fun i => |mu s - 1 / 2 - u (i + 1)|) k, Finset.range_eq_Ico,
      Finset.prod_Ico_add' (fun i => |mu s - 1 / 2 - u i|) 0 k 1]
    rfl
  rw [e]; exact key

theorem lowering_bound : ∀ (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ), Num k r lam u b bv ga h q0 → ∀ ν : Fin (2 * r + k + 1) → ℤ, n1 ν ≤ q0 → ∀ s, (∏ i ∈ Icc 1 k, |lam s + (ν s : ℝ) - 1 / 2 - u i|) / ∏ t ∈ univ.erase s, |lam s + (ν s : ℝ) - 1 - (lam t + (ν t : ℝ))| ≤ b ^ 4 := by
  intro k r lam u b bv ga h q0 hN ν hν s
  obtain ⟨⟨hb, hbv, -, hq, -⟩, hf⟩ := GlobalTheory.T.numericalFamily_shape_gaps k r lam u b bv ga h q0 hN
  obtain ⟨-, -, -, hgap⟩ := hf ν hν
  obtain ⟨hk, hHC, h3, h4, h5, h6, h7, h8, h9, h10, -, -, hga, -, hbig⟩ := hN
  have hq0 : (0 : ℝ) ≤ q0 := Nat.cast_nonneg _
  have key := bound_cast k (2 * r + 1) (2 * r + k + 1) (by omega) lam (fun a => lam a + (ν a : ℝ)) u b bv ga q0 s hk
    (by omega) hHC.1
    (fun a c => by
      obtain ⟨m, hm⟩ := hHC.2 a
      obtain ⟨m', hm'⟩ := hHC.2 c
      exact ⟨m - m', by push_cast at hm hm' ⊢; linarith⟩) h3 h4 h5 h6 h7 h8 h9 h10 (by linarith)
    (fun a => ⟨ν a, by ring⟩) (fun a c hac => by have := hgap a c hac; show _ < _; linarith)
    (by
      have : ((n1 ν : ℕ) : ℝ) ≤ q0 := by exact_mod_cast hν
      refine le_trans (le_of_eq ?_) this
      unfold n1
      push_cast
      refine Finset.sum_congr rfl fun a _ => ?_
      simp)
    (by linarith) (by linarith) (by linarith)
    (fun t ht => by
      rcases lt_or_gt_of_ne ht with hlt | hlt
      · have := hgap t s hlt
        intro e; linarith
      · have := hgap s t hlt
        intro e; linarith)
  refine key.trans ?_
  have he : Real.exp 1 ≤ 3 := Real.exp_one_lt_d9.le.trans (by norm_num)
  have he0 : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
  have hb0 : (0 : ℝ) ≤ b := by linarith
  split_ifs
  · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hs : Real.sqrt k ≤ k := by
      rw [Real.sqrt_le_left (by linarith)]; nlinarith
    have hkn : (k : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega)
    have hp : ((2 * r + k + 1 : ℕ) : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ 7 :=
      le_self_pow₀ (by linarith) (by norm_num)
    have h64 : 64 * Real.exp 1 * Real.sqrt k ≤ b := by
      have : Real.exp 1 * Real.sqrt k ≤ 3 * k := mul_le_mul he hs (Real.sqrt_nonneg _) (by norm_num)
      norm_num at hbig hp hkn ⊢
      nlinarith
    calc _ ≤ b * b ^ 3 := mul_le_mul_of_nonneg_right h64 (by positivity)
      _ = b ^ 4 := by ring
  · have h16 : 16 * Real.exp 1 ≤ b ^ 2 := by nlinarith
    calc _ ≤ b ^ 2 * b ^ 2 := mul_le_mul_of_nonneg_right h16 (by positivity)
      _ = b ^ 4 := by ring

end GlobalTheory.PieriBound
