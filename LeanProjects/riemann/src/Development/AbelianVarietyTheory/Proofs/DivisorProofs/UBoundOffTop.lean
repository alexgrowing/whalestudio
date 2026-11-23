import Mathlib
import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
import Formalism.SharpRestriction.GlobalSchurBounds.MainIn
import Formalism.QuotientMetricDivisors.FinalW
import Formalism.QuotientMetricDivisors.SixthReductionExplicit
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDegreeGapBound
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical

namespace GlobalTheory.LevelLoss

variable {D : D7} {L : SizeData₂ D}

theorem u_bound_off_top (h : SizesAt L) (P : ParameterChoice' D L) (hx : 2 ≤ L.sc.x) (u : D.what₂.Word) (τ : D.what₂.Tau)
    (l : Fin D.R.k) (hl0 : ¬ (l.1 = 0 ∧ τ ∈ topsOf D.host D.eTau)) :
    |(((D.hcW u τ).u l : ℚ) : ℝ)| ≤ 3 * L.sc.b := by
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hm := D.R.two_le_m
  have hb := GlobalTheory.HCEntries.one_le_b L
  have hb1 := GlobalTheory.HCEntries.b_bounds h hx τ ⟨0, by omega⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hE, -, hS, -⟩ := h
  have hS : L.Sc ≤ L.sc.b := by linarith [GlobalTheory.HCEntries.b'_Sc_le hS, GlobalTheory.HCEntries.b'_pos L]
  obtain ⟨r, hr⟩ := l
  rw [abs_le]
  by_cases h0 : r = 0
  · subst h0
    rw [D.hcW_first u τ hr]
    have h2 := L.cloud_v τ ⟨0, by omega⟩
    have h3 : (((D.hc τ).v ⟨0, by omega⟩ : ℚ) : ℝ) < (((D.hc τ).u ⟨0, hr⟩ : ℚ) : ℝ) := by
      exact_mod_cast (D.hc τ).u_gt_v ⟨0, by omega⟩
    refine ⟨by linarith [h2.1], ?_⟩
    have ha : (D.eTau τ : D.R.GG) ∉ D.host.topPlaces := fun ha =>
      hl0 ⟨rfl, by unfold topsOf; exact Finset.mem_filter.2 ⟨Finset.mem_univ _, ha⟩⟩
    have h1 := P.cloud_place_bound τ (by omega) ha
    push_cast at h1
    linarith [h2.2]
  · by_cases hl : r + 1 < D.R.k
    · have := L.cloud_u u τ ⟨r, hr⟩ (by show 1 ≤ r; omega) hl
      constructor <;> linarith [this.1, this.2]
    · obtain rfl : r = D.R.k - 1 := by omega
      rw [D.hcW_last u τ (by omega)]
      have h2 := L.cloud_v τ ⟨D.R.k - 2, by omega⟩
      have h3 : -(((D.hc τ).b ⟨0, by omega⟩ : ℚ) : ℝ) < (((D.hc τ).u ⟨D.R.k - 1, hr⟩ : ℚ) : ℝ) := by
        exact_mod_cast (D.hc τ).u_last_gt (by omega) (by omega)
      have h4 : (((D.hc τ).u ⟨D.R.k - 1, hr⟩ : ℚ) : ℝ) < (((D.hc τ).v ⟨D.R.k - 2, by omega⟩ : ℚ) : ℝ) := by
        have := (D.hc τ).v_gt_u ⟨D.R.k - 2, by omega⟩
        have e : (⟨D.R.k - 2 + 1, by omega⟩ : Fin D.R.k) = ⟨D.R.k - 1, hr⟩ :=
          Fin.ext (by show D.R.k - 2 + 1 = D.R.k - 1; omega)
        simp only at this
        rw [e] at this
        exact_mod_cast this
      constructor <;> linarith [h2.2, hb1.2]

theorem N_le_b (h : SizesAt L) (P : ParameterChoice' D L) : 5 * (D.R.N D.R.m : ℝ) ≤ L.sc.b := by
  have h1 := (GlobalTheory.FockDegreeGap.errors_le h P).2.2
  have hk : (5 : ℝ) ≤ D.R.k := by
    exact_mod_cast (by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega : 5 ≤ D.R.k)
  have h0 : (0 : ℝ) ≤ D.R.N D.R.m := Nat.cast_nonneg _
  nlinarith

theorem true_entry_le (h : SizesAt L) (P : ParameterChoice' D L) (hx : 2 ≤ L.sc.x) (u : D.what₂.Word) (τ : D.what₂.Tau)
    (i : ℕ) (hi : i ≤ D.R.m) (a : Fin (D.R.N i)) (ha : ¬ (a.1 = 0 ∧ τ ∈ topsOf D.host D.eTau)) :
    |((((D.fm u).lam i τ).w a - ((i * (D.R.t + 1) / 2 : ℕ) : ℤ) : ℤ) : ℝ)| ≤ 5 * L.sc.b := by
  have hN := N_le_b h P
  have hNe : (D.R.N D.R.m : ℝ) = D.R.k + D.R.m * (D.R.t + 1) := by unfold Ranks.N; push_cast; ring
  have hk0 : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
  have ht0 : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have hm0 : (0 : ℝ) ≤ (D.R.m : ℝ) * (D.R.t + 1) := by positivity
  have s0 : (0 : ℝ) ≤ ((i * (D.R.t + 1) / 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have s1 : ((i * (D.R.t + 1) / 2 : ℕ) : ℝ) ≤ (D.R.m : ℝ) * (D.R.t + 1) := by
    have : i * (D.R.t + 1) / 2 ≤ D.R.m * (D.R.t + 1) :=
      (Nat.div_le_self _ _).trans (Nat.mul_le_mul_right _ hi)
    exact_mod_cast this
  have e0 : ((((D.fm u).lam i τ).w a : ℤ) : ℝ) = (((((D.fm u).lam i τ).w a : ℤ) : ℚ) : ℝ) := by
    rw [Rat.cast_intCast]
  rw [Int.cast_sub, Int.cast_natCast, e0, (D.fm u).lam_eq i hi τ a]
  split_ifs with hk
  · have b := abs_le.1 (u_bound_off_top h P hx u τ ⟨a.1, hk⟩ ha)
    have a1 : (a.1 : ℝ) ≤ D.R.k := by exact_mod_cast hk.le
    have a0 : (0 : ℝ) ≤ a.1 := Nat.cast_nonneg _
    unfold hcToWeightQ rhoVec
    push_cast
    rw [abs_le]
    constructor <;> linarith [b.1, b.2, GlobalTheory.HCEntries.one_le_b L]
  · have hq := D.R.blk_lt hi a hk
    generalize_proofs
    obtain ⟨w0, w1⟩ := GlobalTheory.HCEntries.wj_bounds h hx ((a.1 - D.R.k) / (D.R.t + 1) + 1) (Nat.le_add_left _ _) hq τ
    rw [GlobalTheory.FockDegreeGap.wj_succ D _ hq] at w0 w1
    rw [D.hcW_e]
    have q1 : (((a.1 - D.R.k) / (D.R.t + 1) + 1 : ℕ) : ℝ) ≤ D.R.m := by exact_mod_cast hq
    have q0 : (1 : ℝ) ≤ (((a.1 - D.R.k) / (D.R.t + 1) + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_add_left _ _
    unfold wG
    generalize ((a.1 - D.R.k) / (D.R.t + 1) + 1 : ℕ) = q at q0 q1 ⊢
    have q2 : (q : ℝ) * (D.R.t + 1) ≤ (D.R.m : ℝ) * (D.R.t + 1) := by gcongr
    have q3 : (1 : ℝ) * (D.R.t + 1) ≤ (q : ℝ) * (D.R.t + 1) := by gcongr
    push_cast
    rw [abs_le]
    constructor <;> linarith

theorem Wtau_le (h : SizesAt L) (P : ParameterChoice' D L) (hx : 2 ≤ L.sc.x) (u : D.what₂.Word) (τ : D.what₂.Tau) :
    (Wtau D u τ : ℝ) ≤ 5 * L.sc.b := by
  have hb := GlobalTheory.HCEntries.one_le_b L
  rw [← Nat.le_floor_iff (by linarith)]
  unfold Wtau
  refine Finset.sup_le fun i hi => Finset.sup_le fun a _ => ?_
  split_ifs with ha
  · exact Nat.zero_le _
  · rw [Nat.le_floor_iff (by linarith), Nat.cast_natAbs, Int.cast_abs]
    exact true_entry_le h P hx u τ i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) a ha

end GlobalTheory.LevelLoss
