import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.MeanLogLeOfBounds
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure
import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoversOfLifts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HostBoundHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundHolds
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CovTop.WtSz

open GlobalTheory.CompHS

theorem abs_ofGaps_le {N : ℕ} (a : ℕ) (g : ℕ → ℤ) (hg : ∀ k, N ≤ k → g k = 0) (j : Fin N) :
    |((ofGaps a g j : ℤ) : ℝ)| ≤ 2 * ∑ k ∈ Finset.range N, |(g k : ℝ)| := by
  have key : ∀ b, b ≤ N ∨ True → ∑ k ∈ Finset.range b, |(g k : ℝ)| ≤ ∑ k ∈ Finset.range N, |(g k : ℝ)| := by
    intro b _
    rcases le_total b N with h | h
    · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 h) (fun _ _ _ => abs_nonneg _)
    · rw [← Finset.sum_range_add_sum_Ico _ h]
      have : ∑ k ∈ Finset.Ico N b, |(g k : ℝ)| = 0 :=
        Finset.sum_eq_zero fun k hk => by simp [hg k (Finset.mem_Ico.1 hk).1]
      rw [this, add_zero]
  have h1 := key a (Or.inr trivial)
  have h2 := key j (Or.inl j.2.le)
  unfold ofGaps
  push_cast
  calc |∑ k ∈ Finset.range a, (g k : ℝ) - ∑ k ∈ Finset.range j, (g k : ℝ)|
      ≤ |∑ k ∈ Finset.range a, (g k : ℝ)| + |∑ k ∈ Finset.range j, (g k : ℝ)| := abs_sub _ _
    _ ≤ ∑ k ∈ Finset.range a, |(g k : ℝ)| + ∑ k ∈ Finset.range j, |(g k : ℝ)| :=
        add_le_add (Finset.abs_sum_le_sum_abs _ _) (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ _ := by linarith

theorem sum_abs_gap_le {N : ℕ} (w : Fin N → ℤ) :
    ∑ k ∈ Finset.range N, |(gap w k : ℝ)| ≤ 2 * ∑ j, |(w j : ℝ)| := by
  let e : ℕ → ℝ := fun k => if h : k < N then |(w ⟨k, h⟩ : ℝ)| else 0
  have he : ∑ j, |(w j : ℝ)| = ∑ k ∈ Finset.range N, e k := by
    rw [← Fin.sum_univ_eq_sum_range]; simp [e]
  have hb : ∀ k, |(gap w k : ℝ)| ≤ e k + e (k + 1) := by
    intro k
    unfold gap
    by_cases h : k + 1 < N
    · simp only [dif_pos h, e, dif_pos (show k < N by omega)]
      push_cast
      exact abs_sub _ _
    · simp only [dif_neg h]
      have : 0 ≤ e k := by simp only [e]; split_ifs <;> simp
      have : 0 ≤ e (k+1) := by simp only [e]; split_ifs <;> simp
      simp; linarith
  have hs : ∑ k ∈ Finset.range N, e (k + 1) ≤ ∑ k ∈ Finset.range N, e k := by
    have := Finset.sum_range_succ' e N
    have h2 := Finset.sum_range_succ e N
    have hN : e N = 0 := by simp [e]
    have h0 : 0 ≤ e 0 := by simp only [e]; split_ifs <;> simp
    linarith
  calc ∑ k ∈ Finset.range N, |(gap w k : ℝ)| ≤ ∑ k ∈ Finset.range N, (e k + e (k + 1)) := Finset.sum_le_sum fun k _ => hb k
    _ ≤ _ := by rw [Finset.sum_add_distrib, he]; linarith

theorem abs_ediv_le (x n : ℤ) (hn : 0 < n) : |((x / n : ℤ) : ℝ)| ≤ |(x : ℝ)| / n + 1 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : ((x / n : ℤ) : ℝ) * n ≤ x := by
    have := Int.ediv_mul_le x hn.ne'; exact_mod_cast this
  have h2 : (x : ℝ) < ((x / n : ℤ) : ℝ) * n + n := by
    have := Int.lt_ediv_add_one_mul_self x hn
    have h3 : (x : ℝ) < ((x / n + 1 : ℤ) : ℝ) * n := by exact_mod_cast this
    push_cast at h3; linarith
  rw [abs_le]
  constructor
  · have : -|(x:ℝ)| ≤ x := neg_abs_le _
    have : ((x / n : ℤ) : ℝ) > (x : ℝ) / n - 1 := by
      rw [gt_iff_lt, sub_lt_iff_lt_add, div_lt_iff₀ hn']; linarith
    have : (x:ℝ)/n ≥ -|(x:ℝ)|/n := by
      apply div_le_div_of_nonneg_right _ hn'.le; linarith
    have : -|(x:ℝ)|/n = -(|(x:ℝ)|/n) := by ring
    linarith
  · have : ((x / n : ℤ) : ℝ) ≤ (x : ℝ) / n := by rw [le_div_iff₀ hn']; exact h1
    have : (x:ℝ)/n ≤ |(x:ℝ)|/n := div_le_div_of_nonneg_right (le_abs_self _) hn'.le
    linarith

end GlobalTheory.CovTop.WtSz

namespace GlobalTheory.CovTop.WtSz

open GlobalTheory.CompHS

theorem gap_sub_const {N : ℕ} (w : Fin N → ℤ) (c : ℤ) (k : ℕ) : gap (fun j => w j - c) k = gap w k := by
  unfold gap; split_ifs <;> ring

theorem gap_eq_zero {N : ℕ} (w : Fin N → ℤ) {k : ℕ} (hk : N ≤ k) : gap w k = 0 := by
  unfold gap; rw [dif_neg (by omega)]

theorem sum_abs_floorGaps_le {N : ℕ} (v w : Fin N → ℤ) (n : ℤ) (hn : 0 < n) (B : ℝ) (a : ℕ)
    (hgv : ∀ k, |(gap v k : ℝ)| ≤ |(gap w k : ℝ)| + B) :
    ∑ j, |(floorGaps a n v j : ℝ)| ≤ 2 * N * ((2 * ∑ j, |(w j : ℝ)| + N * B) / n + N) := by
  have hT' : (0 : ℝ) < n := by exact_mod_cast hn
  have hsum : ∑ k ∈ Finset.range N, |(gap v k : ℝ)| ≤ 2 * ∑ j, |(w j : ℝ)| + N * B := by
    calc ∑ k ∈ Finset.range N, |(gap v k : ℝ)| ≤ ∑ k ∈ Finset.range N, (|(gap w k : ℝ)| + B) :=
          Finset.sum_le_sum fun k _ => hgv k
      _ = ∑ k ∈ Finset.range N, |(gap w k : ℝ)| + N * B := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ _ := by linarith [sum_abs_gap_le w]
  have hG : ∑ k ∈ Finset.range N, |((gap v k / n : ℤ) : ℝ)| ≤ (2 * ∑ j, |(w j : ℝ)| + N * B) / n + N := by
    calc ∑ k ∈ Finset.range N, |((gap v k / n : ℤ) : ℝ)| ≤ ∑ k ∈ Finset.range N, (|(gap v k : ℝ)| / n + 1) :=
          Finset.sum_le_sum fun k _ => abs_ediv_le _ _ hn
      _ = (∑ k ∈ Finset.range N, |(gap v k : ℝ)|) / n + N := by
          rw [Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      _ ≤ _ := by gcongr
  have hent : ∀ j, |(floorGaps a n v j : ℝ)| ≤ 2 * ((2 * ∑ j, |(w j : ℝ)| + N * B) / n + N) := by
    intro j
    refine (abs_ofGaps_le a (fun k => gap v k / n) (fun k hk => ?_) j).trans ?_
    · simp [gap_eq_zero v hk]
    · linarith
  calc ∑ j, |(floorGaps a n v j : ℝ)| ≤ ∑ _j : Fin N, 2 * ((2 * ∑ j, |(w j : ℝ)| + N * B) / n + N) :=
        Finset.sum_le_sum fun j _ => hent j
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

theorem sum_abs_remGaps_le {N : ℕ} (v : Fin N → ℤ) (n : ℤ) (hn : 0 < n) (a : ℕ) :
    ∑ j, |(remGaps a n v j : ℝ)| ≤ 2 * N * N * (n - 1) := by
  have hg : ∀ k, |((gap v k - n * (gap v k / n) : ℤ) : ℝ)| ≤ n - 1 := by
    intro k
    rw [← Int.emod_def]
    have h0 := Int.emod_nonneg (gap v k) hn.ne'
    have h1 := Int.emod_lt_of_pos (gap v k) hn
    rw [abs_of_nonneg (by exact_mod_cast h0)]
    have : gap v k % n ≤ n - 1 := by omega
    exact_mod_cast this
  have hent : ∀ j, |(remGaps a n v j : ℝ)| ≤ 2 * (N * ((n : ℝ) - 1)) := by
    intro j
    refine (abs_ofGaps_le a (fun k => gap v k - n * (gap v k / n)) (fun k hk => ?_) j).trans ?_
    · simp [gap_eq_zero v hk]
    · gcongr
      calc ∑ k ∈ Finset.range N, |((gap v k - n * (gap v k / n) : ℤ) : ℝ)|
          ≤ ∑ _k ∈ Finset.range N, ((n : ℝ) - 1) := Finset.sum_le_sum fun k _ => hg k
        _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  calc ∑ j, |(remGaps a n v j : ℝ)| ≤ ∑ _j : Fin N, 2 * (N * ((n : ℝ) - 1)) :=
        Finset.sum_le_sum fun j _ => hent j
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

theorem T₁_pos (P : WtPar Dw) : 0 < P.T₁ := by unfold WtPar.T₁; positivity

theorem sum_abs_u₁_le (P : WtPar Dw) (τ : Psi H) (w : Fin (Dw.p + Dw.q) → ℤ) (c : ℤ)
    (hu : ∀ j, P.u τ j = w j - c) :
    ∑ j, |(P.u₁ τ j : ℝ)| ≤ 2 * (Dw.p + Dw.q : ℕ) * ((2 * ∑ j, |(w j : ℝ)| +
      (Dw.p + Dw.q : ℕ) * (|(P.c₀ : ℝ)| + 2 * (Dw.p + Dw.q : ℕ) + 2)) / P.T₁ + (Dw.p + Dw.q : ℕ)) := by
  refine sum_abs_floorGaps_le _ w _ (T₁_pos P) _ _ fun k => ?_
  by_cases h : k + 1 < Dw.p + Dw.q
  · rw [P.gap_uMinus_sub_kap τ h]
    have hu' : P.u τ = fun j => w j - c := funext hu
    rw [hu', gap_sub_const]
    push_cast
    refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
    have hN : (0:ℝ) ≤ ((Dw.p + Dw.q : ℕ) : ℝ) := Nat.cast_nonneg _
    push_cast at hN ⊢
    split_ifs
    · calc |-(P.c₀ : ℝ) - (2 * ((Dw.p : ℝ) + Dw.q) - 2)| ≤ |(P.c₀ : ℝ)| + |2 * ((Dw.p : ℝ) + Dw.q) - 2| := by
            rw [show -(P.c₀ : ℝ) - (2 * ((Dw.p : ℝ) + Dw.q) - 2) = -((P.c₀ : ℝ) + (2 * ((Dw.p : ℝ) + Dw.q) - 2)) by ring,
              abs_neg]
            exact abs_add_le _ _
        _ ≤ _ := by
            have : |2 * ((Dw.p : ℝ) + Dw.q) - 2| ≤ 2 * ((Dw.p : ℝ) + Dw.q) + 2 := by
              rw [abs_le]; constructor <;> linarith
            linarith
    · norm_num; linarith [abs_nonneg (P.c₀ : ℝ)]
  · have : gap ((P.uMinus - FlagTan.kap Dw) τ) k = 0 := by unfold gap; rw [dif_neg h]
    rw [this]; simp only [Int.cast_zero, abs_zero]
    have : (0:ℝ) ≤ ((Dw.p + Dw.q : ℕ) : ℝ) := Nat.cast_nonneg _
    positivity

theorem sum_abs_rem_le (P : WtPar Dw) (τ : Psi H) :
    ∑ j, |(P.rem τ j : ℝ)| ≤ 2 * (Dw.p + Dw.q : ℕ) * (Dw.p + Dw.q : ℕ) * (P.T + FlagTan.dimFlag Dw : ℕ) := by
  have h := sum_abs_remGaps_le ((P.uMinus - FlagTan.kap Dw) τ) P.T₁ (T₁_pos P) P.a
  have hT : (P.T₁ : ℝ) - 1 = (P.T + FlagTan.dimFlag Dw : ℕ) := by unfold WtPar.T₁; push_cast; ring
  rw [hT] at h
  exact h

end GlobalTheory.CovTop.WtSz

namespace GlobalTheory.CovTop.WtSz

set_option maxHeartbeats 4000000 in

theorem arith (f r L PP b kap T D c : ℝ) (hf : 8 ≤ f) (hr : 1 ≤ r) (hL : 10 ≤ L)
    (hPP : (f * r * L) ^ 12 ≤ PP) (hb : PP ^ 10 ≤ b) (hk : b ≤ PP * kap) (hT1 : 1 ≤ T) (hD0 : 0 ≤ D) (hDT : D ≤ T)
    (hTup : T ≤ PP ^ 2 * (f * r ^ 2) ^ 2 * r + 1) (hc0 : 0 ≤ c) (hc : c ≤ 22 * f ^ 2 * r ^ 4) :
    2 * r * ((2 * kap + f * r * (c + 2 * r + 2)) / (T + D + 1) + f * r) ≤ (f * r * L) ^ 2 * (kap / T + 1) ∧
    2 * r * ((2 * kap + f * r * (c + 2 * r + 2)) / (T + D + 1) + f * r) + f * (2 * r * r * (T + D)) ≤
      (f * r * L) ^ 2 * (kap / T + 1) := by
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = f * r * L := ⟨_, rfl⟩
  rw [← hZ] at hPP ⊢
  have hfr : 8 ≤ f * r := by nlinarith
  have hZ80 : 80 ≤ Z := by rw [hZ]; nlinarith
  have hZ1 : 1 ≤ Z := by linarith
  have hfZ : f ≤ Z := by rw [hZ]; nlinarith
  have hrZ : r ≤ Z := by rw [hZ]; nlinarith
  have hfrZ : f * r ≤ Z := by rw [hZ]; nlinarith
  have hZpow : ∀ n m : ℕ, n ≤ m → Z ^ n ≤ Z ^ m := fun n m h => pow_le_pow_right₀ hZ1 h
  have hPP1 : 1 ≤ PP := le_trans (one_le_pow₀ hZ1) hPP
  have hPPZ : Z ^ 12 ≤ PP := hPP

  have hb0 : 0 < b := lt_of_lt_of_le (by positivity) hb
  have hkap9 : PP ^ 9 ≤ kap := by
    have : PP * PP ^ 9 ≤ PP * kap := by nlinarith [pow_succ' PP 9]
    exact le_of_mul_le_mul_left this (by linarith)
  have hPPpow : ∀ n m : ℕ, n ≤ m → PP ^ n ≤ PP ^ m := fun n m h => pow_le_pow_right₀ hPP1 h

  have hB : f * r * (c + 2 * r + 2) ≤ kap := by
    have h1 : f * r * (c + 2 * r + 2) ≤ f * r * (26 * f ^ 2 * r ^ 4) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have : 2 * r + 2 ≤ 4 * f ^ 2 * r ^ 4 := by
        have : r ≤ r ^ 4 := by nlinarith [pow_le_pow_right₀ hr (show 1 ≤ 4 by norm_num), pow_one r]
        have : 1 ≤ f ^ 2 := by nlinarith
        have : r ^ 4 ≤ f ^ 2 * r ^ 4 := by nlinarith [pow_pos (by linarith : (0:ℝ) < r) 4]
        nlinarith [pow_pos (by linarith : (0:ℝ) < r) 4]
      linarith
    have h2 : f * r * (26 * f ^ 2 * r ^ 4) ≤ 26 * Z ^ 5 := by
      have : f * r * (f ^ 2 * r ^ 4) ≤ Z ^ 5 := by
        have e : f * r * (f ^ 2 * r ^ 4) = (f * r) ^ 3 * r ^ 2 := by ring
        rw [e]
        calc (f * r) ^ 3 * r ^ 2 ≤ Z ^ 3 * Z ^ 2 := by gcongr
          _ = Z ^ 5 := by ring
      linarith
    have h3 : 26 * Z ^ 5 ≤ Z ^ 12 := by
      have : 26 ≤ Z ^ 7 := by nlinarith [hZpow 1 7 (by norm_num), pow_one Z]
      have e : Z ^ 12 = Z ^ 7 * Z ^ 5 := by ring
      rw [e]; nlinarith [pow_pos (by linarith : (0:ℝ) < Z) 5]
    nlinarith [hPPpow 1 9 (by norm_num), pow_one PP]

  have hT3 : T ≤ 2 * PP ^ 3 := by
    have h1 : (f * r ^ 2) ^ 2 * r ≤ Z ^ 5 := by
      have e : (f * r ^ 2) ^ 2 * r = (f * r) ^ 2 * r ^ 3 := by ring
      rw [e]
      calc (f * r) ^ 2 * r ^ 3 ≤ Z ^ 2 * Z ^ 3 := by gcongr
        _ = Z ^ 5 := by ring
    have h2 : Z ^ 5 ≤ PP := (hZpow 5 12 (by norm_num)).trans hPPZ
    have h3 : PP ^ 2 * ((f * r ^ 2) ^ 2 * r) ≤ PP ^ 2 * PP := by gcongr; linarith
    have h4 : 1 ≤ PP ^ 3 := one_le_pow₀ hPP1
    nlinarith
  have hT0 : 0 < T := by linarith
  have hT₁ : T ≤ T + D + 1 := by linarith

  have hU1 : 2 * r * ((2 * kap + f * r * (c + 2 * r + 2)) / (T + D + 1) + f * r) ≤ 6 * r * (kap / T) + 2 * f * r ^ 2 := by
    have hkap0 : 0 ≤ kap := le_trans (by positivity) hkap9
    have : (2 * kap + f * r * (c + 2 * r + 2)) / (T + D + 1) ≤ 3 * kap / T := by
      rw [div_le_div_iff₀ (by linarith) hT0]
      nlinarith
    have e : 3 * kap / T = 3 * (kap / T) := by ring
    nlinarith
  have hq0 : 0 ≤ kap / T := div_nonneg (le_trans (by positivity) hkap9) hT0.le
  have hfL : 12 ≤ f * L ^ 2 := by nlinarith
  have hfr2 : 0 ≤ f * r ^ 2 := by positivity
  have hZsq : Z ^ 2 = (f * L ^ 2) * (f * r ^ 2) := by rw [hZ]; ring
  have hmul : 12 * (f * r ^ 2) ≤ (f * L ^ 2) * (f * r ^ 2) := mul_le_mul_of_nonneg_right hfL hfr2
  have hZ2 : 2 * f * r ^ 2 ≤ Z ^ 2 := by
    rw [hZsq]; have : 0 ≤ f * r ^ 2 := hfr2; linarith
  have h6r : 6 * r ≤ Z ^ 2 / 2 := by
    have : r ≤ f * r ^ 2 := by nlinarith
    rw [hZsq]; linarith

  have hR : f * (2 * r * r * (T + D)) ≤ Z ^ 2 / 2 * (kap / T) := by
    have h1 : f * (2 * r * r * (T + D)) ≤ 4 * f * r ^ 2 * T := by nlinarith [mul_pos (by linarith : (0:ℝ) < f) (by linarith : (0:ℝ) < r)]
    have h2 : 4 * f * r ^ 2 * T ≤ kap / T := by
      rw [le_div_iff₀ hT0]
      have hT2 : T * T ≤ 4 * PP ^ 6 := by nlinarith
      have h16 : 16 * f * r ^ 2 ≤ PP := by
        have : 16 * f * r ^ 2 ≤ Z ^ 12 := by
          have : f * r ^ 2 ≤ Z ^ 3 := by
            calc f * r ^ 2 ≤ Z * Z ^ 2 := by gcongr
              _ = Z ^ 3 := by ring
          have : 16 ≤ Z ^ 9 := by nlinarith [hZpow 1 9 (by norm_num), pow_one Z]
          have e : Z ^ 12 = Z ^ 9 * Z ^ 3 := by ring
          rw [e]; nlinarith [pow_pos (by linarith : (0:ℝ) < Z) 3, mul_pos (by linarith : (0:ℝ) < f) (by positivity : (0:ℝ) < r ^ 2)]
        linarith
      have : 4 * f * r ^ 2 * T * T ≤ 4 * f * r ^ 2 * (4 * PP ^ 6) := by
        have : 0 ≤ 4 * f * r ^ 2 := by positivity
        rw [mul_assoc (4 * f * r ^ 2)]; exact mul_le_mul_of_nonneg_left hT2 this
      have : 4 * f * r ^ 2 * (4 * PP ^ 6) ≤ PP * PP ^ 6 := by nlinarith [pow_pos (by linarith : (0:ℝ) < PP) 6]
      have : PP * PP ^ 6 ≤ PP ^ 9 := by rw [← pow_succ']; exact hPPpow 7 9 (by norm_num)
      linarith
    have h3 : kap / T ≤ Z ^ 2 / 2 * (kap / T) := by
      have : 1 ≤ Z ^ 2 / 2 := by nlinarith
      nlinarith
    linarith
  have a1 : 6 * r * (kap / T) ≤ Z ^ 2 / 2 * (kap / T) := mul_le_mul_of_nonneg_right h6r hq0
  have a2 : Z ^ 2 / 2 * (kap / T) ≤ Z ^ 2 * (kap / T) := mul_le_mul_of_nonneg_right (by nlinarith) hq0
  have e : Z ^ 2 * (kap / T + 1) = Z ^ 2 * (kap / T) + Z ^ 2 := by ring
  rw [e]
  refine ⟨by linarith, by linarith⟩

end GlobalTheory.CovTop.WtSz

namespace GlobalTheory.CovTop.WtSz

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

set_option maxHeartbeats 1000000 in

theorem at_pt (PP A A' : ℝ) (hi : (i : ℕ) + 1 < D.R.m) (hS : SizeAt p i PP A) (hH : HostNum D L PP A' 10)
    (hW : WtNum p i PP) :
    ∀ la ∈ ({(⟨uW p i, cZero D ((i : ℕ) + 1), D.R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁,
      (⟨uW p i, cZero D ((i : ℕ) + 1), D.R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₂} : Set (AllWt.Weight (dat p i))),
      ∑ τ, ∑ k, |(la τ k : ℝ)| ≤ zBase L ^ 2 * (kap p i / lenT p i PP + 1) := by
  set P : WtPar (dat p i) := ⟨uW p i, cZero D ((i : ℕ) + 1), D.R.k - 2, lenT p i PP⟩ with hP
  have hN : (((dat p i).p + (dat p i).q : ℕ) : ℝ) = D.R.r := by rw [hW.sig.2.2]
  have hcard : (Fintype.card (Psi p.T.Q.H) : ℝ) = D.R.f := by rw [← Nat.card_eq_fintype_card, hW.card]
  have hRk : D.R.k ≤ D.R.r ∧ 1 ≤ D.R.m ∧ 1 ≤ D.R.r := by
    have := D.R.two_le_m; unfold Ranks.r; omega
  have hDim : CompHt.dimFlag (dat p i) = FlagTan.dimFlag (dat p i) := GlobalTheory.CompHS.dimFlag_eq _
  obtain ⟨⟨u1, hu1⟩, hq⟩ := hS.2.2.2.2.2.2 hi
  have hT3 := (hq u1 hu1).1
  rw [hDim] at hT3
  have hc := cZero_spec D ((i : ℕ) + 1)
  have hc0 : (0 : ℝ) ≤ (cZero D ((i : ℕ) + 1) : ℝ) := by exact_mod_cast hc.2.1
  have hc1 : (cZero D ((i : ℕ) + 1) : ℝ) ≤ 22 * (D.R.f : ℝ) ^ 2 * (D.R.r : ℝ) ^ 4 := by exact_mod_cast hc.2.2

  have hPPx := hH.poly.2.1
  have hroom := hH.room
  have hZ12 := hH.ppLow
  have hPP0 : 0 ≤ PP := le_trans (by unfold zBase; positivity) hZ12
  have hroom' : (L.sc.x ^ A') ^ (10 : ℕ) ≤ L.sc.b := by
    have := Real.rpow_natCast (L.sc.x ^ A') 10
    push_cast at this
    rwa [this] at hroom
  have hb10 : PP ^ 10 ≤ L.sc.b := (pow_le_pow_left₀ hPP0 hPPx 10).trans hroom'

  have hTup : (lenT p i PP : ℝ) ≤ PP ^ 2 * ((D.R.f : ℝ) * (D.R.r : ℝ) ^ 2) ^ 2 * D.R.r + 1 := by
    have hd : (CompHt.dimFlag (dat p i) : ℝ) ≤ (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 := by
      rw [hW.dim]
      have : D.R.r.choose 2 ≤ D.R.r ^ 2 := by
        rw [Nat.choose_two_right, sq]; exact (Nat.div_le_self _ _).trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
      exact_mod_cast Nat.mul_le_mul_left _ this
    have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast hRk.2.1
    have hk : (D.R.k : ℝ) ≤ D.R.r := by exact_mod_cast hRk.1
    have hx : 0 ≤ PP ^ 2 * (CompHt.dimFlag (dat p i) : ℝ) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ) := by positivity
    have h1 := Nat.ceil_lt_add_one hx
    have h2 : PP ^ 2 * (CompHt.dimFlag (dat p i) : ℝ) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ) ≤
        PP ^ 2 * ((D.R.f : ℝ) * (D.R.r : ℝ) ^ 2) ^ 2 * D.R.r := by
      rw [div_le_iff₀ (by linarith)]
      have a : (CompHt.dimFlag (dat p i) : ℝ) ^ 2 ≤ ((D.R.f : ℝ) * (D.R.r : ℝ) ^ 2) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hd 2
      have b : PP ^ 2 * (CompHt.dimFlag (dat p i) : ℝ) ^ 2 * (D.R.k : ℝ) ≤ PP ^ 2 * ((D.R.f : ℝ) * (D.R.r : ℝ) ^ 2) ^ 2 * D.R.r := by
        gcongr
      have c : 0 ≤ PP ^ 2 * ((D.R.f : ℝ) * (D.R.r : ℝ) ^ 2) ^ 2 * D.R.r := by positivity
      nlinarith
    unfold lenT
    linarith
  have hA := arith (D.R.f : ℝ) (D.R.r : ℝ) L.sc.L PP L.sc.b (kap p i) (lenT p i PP : ℝ) (FlagTan.dimFlag (dat p i) : ℝ)
    (cZero D ((i : ℕ) + 1) : ℝ) (by exact_mod_cast hH.f8) (by exact_mod_cast hRk.2.2) hH.big.2.1 (by unfold zBase at hZ12; exact hZ12)
    hb10 hS.2.2.2.2.2.1 (by exact_mod_cast (show 1 ≤ lenT p i PP by omega)) (by positivity)
    (by exact_mod_cast (show FlagTan.dimFlag (dat p i) ≤ lenT p i PP by omega)) hTup hc0 hc1
  have hZ : zBase L = (D.R.f : ℝ) * D.R.r * L.sc.L := rfl
  rw [hZ]

  have hT₁ : (P.T₁ : ℝ) = (lenT p i PP : ℝ) + (FlagTan.dimFlag (dat p i) : ℝ) + 1 := by
    simp [WtPar.T₁, hP]
  have hS1 : ∑ τ, ∑ j, |(P.u₁ τ j : ℝ)| ≤ 2 * (D.R.r : ℝ) * ((2 * kap p i + D.R.f * D.R.r *
      ((cZero D ((i : ℕ) + 1) : ℝ) + 2 * D.R.r + 2)) / ((lenT p i PP : ℝ) + (FlagTan.dimFlag (dat p i) : ℝ) + 1) +
      D.R.f * D.R.r) := by
    calc ∑ τ, ∑ j, |(P.u₁ τ j : ℝ)| ≤ ∑ τ, 2 * (((dat p i).p + (dat p i).q : ℕ) : ℝ) *
          ((2 * ∑ j, |(laOf (dat p i) (wtA (p.κ i)) (p.κ i).n τ j : ℝ)| + (((dat p i).p + (dat p i).q : ℕ) : ℝ) *
            (|(P.c₀ : ℝ)| + 2 * (((dat p i).p + (dat p i).q : ℕ) : ℝ) + 2)) / P.T₁ + (((dat p i).p + (dat p i).q : ℕ) : ℝ)) :=
          Finset.sum_le_sum fun τ _ => sum_abs_u₁_le P τ _ (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ)
            (fun j => rfl)
      _ = _ := by
          rw [hN, hT₁, show P.c₀ = cZero D ((i : ℕ) + 1) from rfl, abs_of_nonneg hc0]
          simp only [mul_add, add_div, mul_div_assoc, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div,
            Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
          rw [show kap p i = ∑ τ : Psi p.T.Q.H, ∑ k, |(laOf (dat p i) (wtA (p.κ i)) (p.κ i).n τ k : ℝ)| from rfl]
          ring
  have hS2 : ∑ τ, ∑ j, |(P.rem τ j : ℝ)| ≤ D.R.f * (2 * D.R.r * D.R.r * ((lenT p i PP : ℝ) + FlagTan.dimFlag (dat p i))) := by
    calc ∑ τ, ∑ j, |(P.rem τ j : ℝ)| ≤ ∑ _τ : Psi p.T.Q.H, 2 * (((dat p i).p + (dat p i).q : ℕ) : ℝ) *
          (((dat p i).p + (dat p i).q : ℕ) : ℝ) * ((P.T + FlagTan.dimFlag (dat p i) : ℕ) : ℝ) :=
          Finset.sum_le_sum fun τ _ => sum_abs_rem_le P τ
      _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard, hN]
          push_cast; rfl
  have hS3 : ∑ τ, ∑ j, |(P.u₂ τ j : ℝ)| ≤ ∑ τ, ∑ j, |(P.u₁ τ j : ℝ)| + ∑ τ, ∑ j, |(P.rem τ j : ℝ)| := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun τ _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    have : (P.u₂ τ j : ℝ) = (P.u₁ τ j : ℝ) + (P.rem τ j : ℝ) := by
      simp [WtPar.u₂]
    rw [this]; exact abs_add_le _ _
  intro la hla
  rcases hla with rfl | rfl
  · exact hS1.trans hA.1
  · exact hS3.trans (by linarith [hA.2])

end GlobalTheory.CovTop.WtSz

namespace GlobalTheory.CovTop.WtSz

set_option maxHeartbeats 1000000 in

theorem wts_le : Size → Covers fun Fm x _ ι p i Y PP _ => ∀ la ∈ ({(⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁, (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₂} : Set (AllWt.Weight (dat p i))), ∑ τ, ∑ k, |(la τ k : ℝ)| ≤ zBase (Fm.L x ι) ^ 2 * (kap p i / lenT p i PP + 1) := by
  intro hS
  have hL : Lifts fun Fm x _ ι p i PP _ => (∃ A, SizeAt p i PP A) ∧ (∃ A, HostNum (Fm.D x ι) (Fm.L x ι) PP A 10) ∧
      WtNum p i PP := by
    refine Formalism.MainNotions.Closed.imp (Formalism.MainNotions.Closed.and hS (Formalism.MainNotions.Closed.and (GlobalTheory.CovTop.Sizes.hostN 10) GlobalTheory.CovTop.WtShape.wtN))
      fun Fm CH _ h => ?_
    obtain ⟨⟨C1, _, a1, ha1⟩, ⟨C2, _, a2, ha2⟩, ⟨C3, _, a3, ha3⟩⟩ := h
    exact ⟨0, le_rfl, max a1 (max a2 a3), fun x hx hle ι p hp i =>
      ⟨⟨C1, ha1 x hx ((le_max_left _ _).trans hle) ι p hp i⟩,
        ⟨C2, ha2 x hx (((le_max_left _ _).trans (le_max_right _ _)).trans hle) ι p hp i⟩,
        ha3 x hx (((le_max_right _ _).trans (le_max_right _ _)).trans hle) ι p hp i⟩⟩
  exact CovSz.covers_of_lifts hL fun Fm x hx ι p i _ _ h hi _ _ =>
    at_pt p i _ h.1.choose h.2.1.choose hi h.1.choose_spec h.2.1.choose_spec h.2.2

end GlobalTheory.CovTop.WtSz
