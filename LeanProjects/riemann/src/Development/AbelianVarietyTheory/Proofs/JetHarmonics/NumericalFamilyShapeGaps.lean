import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.NumFam

theorem eps_adj (k r : ℕ) (a c : Fin (2 * r + k + 1)) (ha : k ≤ a.val + 1) (hc : c.val = a.val + 1) :
    PI.BesselPeriodGGP.eps48 k r a ≠ PI.BesselPeriodGGP.eps48 k r c := by
  have h1 : ¬ a.val < k - 1 := by omega
  have h2 : ¬ c.val < k - 1 := by omega
  simp only [PI.BesselPeriodGGP.eps48]
  rw [if_neg h1, if_neg h2, hc]
  rcases Nat.mod_two_eq_zero_or_one (a.val - (k - 1)) with h3 | h3
  · have h4 : (a.val + 1 - (k - 1)) % 2 = 1 := by omega
    simp [h3, h4]
  · have h4 : (a.val + 1 - (k - 1)) % 2 = 0 := by omega
    simp [h3, h4]

theorem abs_le_of_lOneNorm_le_coord {n : ℕ} (ν : Fin n → ℤ) (q0 : ℕ) (h : n1 ν ≤ q0) (a : Fin n) : |(ν a : ℝ)| ≤ q0 := by
  have h1 : (ν a).natAbs ≤ n1 ν := by
    unfold n1
    exact Finset.single_le_sum (f := fun i => (ν i).natAbs) (fun i _ => Nat.zero_le _) (Finset.mem_univ a)
  have h2 : |(ν a : ℝ)| = ((ν a).natAbs : ℝ) := by
    rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
  rw [h2]
  exact_mod_cast h1.trans h

theorem gapOK_mono (k r : ℕ) {h h' : ℝ} (hh : h ≤ h') (H : GapOK k r h) : GapOK k r h' := by
  obtain ⟨h1, h2, h3, h4⟩ := H
  have ha : aOf r h ≤ aOf r h' := by
    unfold aOf
    gcongr
  exact ⟨h1, h2.trans hh, h3.trans ha, h4.trans ha⟩

private lemma le_bv_and_lam_gap_of_num (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ)
    (q0 : ℕ) (H : Num k r lam u b bv ga h q0) :
    h ≤ bv ∧ ∀ a c : Fin (2 * r + k + 1), a < c → 100 * ((q0 : ℝ) + 1) ≤ lam a - lam c := by
  obtain ⟨hk, ⟨hanti, -⟩, -, -, -, hcl, hnd, -, -, hga, hgap, -, hq1, hq2, -⟩ := H
  have hhb : h ≤ bv := by
    have he := eps_adj k r ⟨k - 1, by omega⟩ ⟨k, by omega⟩ (show k ≤ k - 1 + 1 by omega)
      (show k = k - 1 + 1 by omega)
    have h0 := hnd ⟨k - 1, by omega⟩ (show k ≤ k - 1 + 1 by omega)
    have h1 := hnd ⟨k, by omega⟩ (show k ≤ k + 1 by omega)
    have hg := hgap _ _ he
    have hb : |lam ⟨k - 1, by omega⟩ - lam ⟨k, by omega⟩| ≤ bv :=
      abs_sub_le_iff.mpr ⟨by linarith [h0.1, h0.2, h1.1, h1.2], by linarith [h0.1, h0.2, h1.1, h1.2]⟩
    linarith
  have hadj : ∀ a c : Fin (2 * r + k + 1), c.val = a.val + 1 →
      100 * ((q0 : ℝ) + 1) ≤ lam a - lam c := by
    intro a c hac
    have hlt : a < c := Fin.lt_def.mpr (by omega)
    have hlam : lam c < lam a := hanti hlt
    by_cases h1 : k ≤ a.val + 1
    · have hg := hgap a c (eps_adj k r a c h1 hac)
      rw [abs_of_pos (by linarith)] at hg
      linarith
    · by_cases h2 : c.val + 1 < k
      · linarith [hga a c hlt h2]
      · have h3 := hcl a (by omega)
        have h4 := hnd c (by omega)
        linarith [h3.1, h4.2]
  refine ⟨hhb, fun a c hac => ?_⟩
  have h5 : a.val < c.val := hac
  have hcN := c.isLt
  have hle : a ≤ ⟨c.val - 1, by omega⟩ := Fin.le_def.mpr (show a.val ≤ c.val - 1 by omega)
  have h6 := hadj ⟨c.val - 1, by omega⟩ c (show c.val = c.val - 1 + 1 by omega)
  have h7 := hanti.antitone hle
  linarith

theorem num_fam : ∀ (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ), Num k r lam u b bv ga h q0 → (bv ≤ b ∧ (1000000 : ℝ) ≤ bv ∧ ((2 * r + k + 1) : ℝ) ≤ b ∧ 100 * (q0 : ℝ) ≤ bv ∧ GapOK k r (h / 2)) ∧ ∀ ν : Fin (2 * r + k + 1) → ℤ, n1 ν ≤ q0 → Formalism.QuantumDeterminants.IsHCParam (fun a => lam a + (ν a : ℝ)) ∧ Shape (PI.BesselPeriodGGP.eps48 k r) k (fun a => lam a + (ν a : ℝ)) bv ∧ Formalism.QuantumDeterminants.GapAtLeast (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ)) (h / 2) ∧ ∀ a c, a < c → 2 ≤ (lam a + (ν a : ℝ)) - (lam c + (ν c : ℝ)) := by
  intro k r lam u b bv ga h q0 H
  obtain ⟨hhb, hgaps⟩ := le_bv_and_lam_gap_of_num k r lam u b bv ga h q0 H
  obtain ⟨hk, ⟨hanti, hint⟩, -, -, -, hcl, hnd, hlb, -, -, hgap, hok, hq1, hq2, hbv⟩ := H
  have hq0 : (0 : ℝ) ≤ q0 := Nat.cast_nonneg _
  have hN1 : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * r + k + 1)
  have hN7 : ((2 * r + k + 1 : ℕ) : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ 7 := le_self_pow₀ hN1 (by norm_num)
  have hNc : ((2 * r + k + 1 : ℕ) : ℝ) = 2 * (r : ℝ) + k + 1 := by push_cast; ring
  have hL := hnd ⟨2 * r + k, by omega⟩ (show k ≤ 2 * r + k + 1 by omega)
  have hLb := hlb ⟨2 * r + k, by omega⟩
  have hLa := neg_le_abs (lam ⟨2 * r + k, by omega⟩)
  have hbvb : bv ≤ b := by linarith [hL.2]
  have h100 : 100 * (q0 : ℝ) ≤ bv := by linarith
  refine ⟨⟨hbvb, by linarith, by linarith, h100, gapOK_mono k r (by linarith) hok⟩, fun ν hν => ?_⟩
  have hνb : ∀ a, -(q0 : ℝ) ≤ ν a ∧ (ν a : ℝ) ≤ q0 := fun a => abs_le.mp (abs_le_of_lOneNorm_le_coord ν q0 hν a)
  have hgap2 : ∀ a c : Fin (2 * r + k + 1), a < c → 2 ≤ (lam a + (ν a : ℝ)) - (lam c + (ν c : ℝ)) := by
    intro a c hac
    linarith [hgaps a c hac, (hνb a).1, (hνb a).2, (hνb c).1, (hνb c).2]
  refine ⟨⟨fun a c hac => ?_, fun a => ?_⟩, ⟨hk, by omega, fun a c hac => hgap2 a c hac, fun a ha => ?_,
    fun a ha => ?_, hbv⟩, fun a c he => ?_, fun a c hac => hgap2 a c hac⟩
  · show lam c + (ν c : ℝ) < lam a + ν a
    linarith [hgap2 a c hac]
  · obtain ⟨m, hm⟩ := hint a
    refine ⟨m + ν a, ?_⟩
    show lam a + (ν a : ℝ) - (((2 * r + k + 1 : ℕ) : ℝ) - 1) / 2 = ((m + ν a : ℤ) : ℝ)
    push_cast
    linarith
  · refine ⟨?_, ?_, ?_⟩
    · simp [PI.BesselPeriodGGP.eps48, show a.val < k - 1 by omega]
    · show -(bv / 100) ≤ lam a + (ν a : ℝ)
      linarith [(hcl a ha).1, (hνb a).1]
    · show lam a + (ν a : ℝ) ≤ bv / 8 + bv / 100
      linarith [(hcl a ha).2, (hνb a).2]
  · refine ⟨?_, ?_⟩
    · show -2 * bv - bv / 100 ≤ lam a + (ν a : ℝ)
      linarith [(hnd a ha).1, (hνb a).1]
    · show lam a + (ν a : ℝ) ≤ -bv + bv / 100
      linarith [(hnd a ha).2, (hνb a).2]
  · show h / 2 ≤ |(lam a + (ν a : ℝ)) - (lam c + (ν c : ℝ))|
    have hg := hgap a c he
    rcases le_abs.mp hg with h1 | h1
    · exact le_abs.mpr (Or.inl (by linarith [(hνb a).1, (hνb a).2, (hνb c).1, (hνb c).2]))
    · exact le_abs.mpr (Or.inr (by linarith [(hνb a).1, (hνb a).2, (hνb c).1, (hνb c).2]))

end GlobalTheory.NumFam
