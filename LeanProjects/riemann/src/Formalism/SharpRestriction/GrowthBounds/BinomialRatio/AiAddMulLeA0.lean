import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.UpperCountOfTopRows
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CoarseDegreeAlternative
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.TopDegreeLeTwoB
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.LeAndHalfLeProdOneSubExpNegOfBounds

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

theorem coarse_ratio_small {Al Ai Pl Pi bl bi b' be k p : ℝ} (hAl : 0 ≤ Al) (hb : 0 < b') (_hbe0 : 0 ≤ be) (hbe : be ≤ 1 / 12)
    (hPi : 0 < Pi) (hp : 0 < p) (hP : p * Pi ≤ Pl) (h1 : Al * Pl ≤ bl) (h2 : bl ≤ b' * (1 + be))
    (h3 : bi - k * Pi < Ai * Pi) (h4 : b' * (1 - be) ≤ bi) : Al ≤ 2 * (Ai + k) / p := by
  rw [le_div_iff₀ hp]
  have e1 : Al * (p * Pi) ≤ Al * Pl := mul_le_mul_of_nonneg_left hP hAl
  have e2 : b' * be ≤ b' * (1 / 12) := mul_le_mul_of_nonneg_left hbe hb.le
  have e3 : Al * p * Pi ≤ 2 * (Ai + k) * Pi := by nlinarith
  exact le_of_mul_le_mul_right e3 hPi

theorem Ai_add_mul_le_A0 {Ai A0 de ε k p N1 La s : ℝ} (hAi : 0 ≤ Ai) (hA : Ai * (1 + de) < A0) (hde : 40 * ε ≤ de)
    (hde6 : de < 1 / 6) (hε : ε = N1 * La / k) (hk : 5 ≤ k) (hkA : k ≤ A0) (hp : k ^ 2 ≤ p) (hLa : 1 ≤ La)
    (hN1 : 1 ≤ N1) (_hs0 : 0 ≤ s) (hs : s ≤ N1) :
    Ai + s * (2 * (Ai + k) / p + 2 * La * A0 / k) ≤ A0 := by
  have hk0 : 0 < k := by linarith
  have hp0 : 0 < p := lt_of_lt_of_le (by positivity) hp
  have hA0 : 0 < A0 := by linarith
  have hε0 : 0 ≤ ε := by rw [hε]; positivity
  have hde0 : 0 ≤ de := by linarith
  have hAiA : Ai ≤ A0 := by nlinarith

  have h1 : A0 * de < (A0 - Ai) * (1 + de) := by nlinarith
  have h2 : (A0 - Ai) * (1 + de) ≤ (A0 - Ai) * (7 / 6) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h3 : A0 * (40 * ε) ≤ A0 * de := mul_le_mul_of_nonneg_left hde hA0.le
  have h4 : 34 * (ε * A0) ≤ A0 - Ai := by nlinarith

  have c1 : 2 * (Ai + k) / p ≤ 4 * A0 / k ^ 2 := by
    rw [div_le_div_iff₀ hp0 (by positivity)]
    have : 2 * (Ai + k) ≤ 4 * A0 := by linarith
    calc 2 * (Ai + k) * k ^ 2 ≤ 4 * A0 * k ^ 2 := mul_le_mul_of_nonneg_right this (by positivity)
      _ ≤ 4 * A0 * p := mul_le_mul_of_nonneg_left hp (by positivity)
  have c2 : 4 * A0 / k ^ 2 ≤ La * A0 / k := by
    rw [div_le_div_iff₀ (by positivity) hk0]
    have : 4 * A0 * k ≤ La * A0 * k * k := by
      have : 4 * A0 ≤ La * A0 * k := by nlinarith [mul_le_mul hLa hk (by norm_num) (by linarith)]
      nlinarith
    nlinarith
  have c3 : 2 * (Ai + k) / p + 2 * La * A0 / k ≤ 3 * (La * A0 / k) := by
    have : 2 * La * A0 / k = 2 * (La * A0 / k) := by ring
    linarith
  have c30 : 0 ≤ La * A0 / k := by positivity
  have c4 : s * (2 * (Ai + k) / p + 2 * La * A0 / k) ≤ N1 * (3 * (La * A0 / k)) :=
    mul_le_mul hs c3 (by positivity) (by linarith)
  have c5 : N1 * (3 * (La * A0 / k)) = 3 * (ε * A0) := by rw [hε]; ring
  have c6 : 0 ≤ ε * A0 := by positivity
  linarith

variable {C0 Cde CE1 CE2 H : ℝ} {X : Loc}

theorem partial_width_le_cap [NeZero X.m] (hH : 1 ≤ H) (h : Std C0 Cde CE1 CE2 H X) (j : Fin (numSeg X.TT))
    (b : SegBlock (segS X.TT j) X.m) (hK : Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b)
    (i : Fin (segS X.TT j)) (hi : i.val < (X.seg C0 CE1 CE2 j).sigma) (n : ℕ) (hn : n ≤ i.val + 1) :
    (∑ l : Fin (segS X.TT j), if l.val < i.val + 1 then (b.w l : ℤ) else 0) ≤ cap X.p (X.seg C0 CE1 CE2 j) b n := by
  obtain ⟨hd, -, hSt, -⟩ := hK
  set S := X.seg C0 CE1 CE2 j with hS

  have hk5 := h.k5
  have hk0 : 0 < X.k := by linarith
  have hp0 : (0 : ℝ) < X.p := by linarith [h.p1]
  have hde : 40 * eps X C0 ≤ X.de C0 Cde := by
    have := h.LaK
    unfold eps
    calc 40 * (X.N1 * X.La C0 / X.k) = 40 * X.N1 * X.La C0 / X.k := by ring
      _ ≤ _ := this
  have hbe12 : be X C0 ≤ 1 / 12 := by
    have h1 := h.beLe
    have h2 := h.de6
    have h3 : 0 ≤ 18 * X.N1 * X.La C0 / X.k := by
      have := h.La1
      positivity
    linarith
  have hA0k : X.k ≤ (S.A0 X.p : ℝ) := by
    refine le_trans ?_ (h.half_ratio_le_segment_base_of_std j)
    have hQ0 : 0 < X.Q := by linarith [h.Q1]
    rw [le_div_iff₀ (by positivity)]
    have h1 := h.kQ hH
    have h2 := h.ba
    have h3 : X.k * (2 * X.Q) ≤ X.k ^ 3 * X.Q := by
      have hk2 : (2 : ℝ) ≤ X.k ^ 2 := by nlinarith
      calc X.k * (2 * X.Q) = (X.k * X.Q) * 2 := by ring
        _ ≤ (X.k * X.Q) * X.k ^ 2 := mul_le_mul_of_nonneg_left hk2 (mul_pos hk0 hQ0).le
        _ = X.k ^ 3 * X.Q := by ring
    linarith
  have hcb : ∀ l : Fin (segS X.TT j),
      (coarseA X.p S b l : ℝ) * ((X.p ^ (segG X.TT j - (segDists X.TT j).get l) : ℕ) : ℝ) ≤ X.bT (segPos X.TT j l) ∧
      (X.bT (segPos X.TT j l) : ℝ) - ((X.m : ℝ) + 1) * ((X.p ^ (segG X.TT j - (segDists X.TT j).get l) : ℕ) : ℝ) <
        (coarseA X.p S b l : ℝ) * ((X.p ^ (segG X.TT j - (segDists X.TT j).get l) : ℕ) : ℝ) := fun l =>
    coarse_bounds (X.bT (segPos X.TT j l)) (X.p ^ (segG X.TT j - (segDists X.TT j).get l)) (b.rz l)
      (fun c => (hd.1 l c).1) (hd.2.1 l).1 (hd.2.1 l).2
  have hAi := (coarse_degree_alternative hH h j b hd i).1 hi
  set c1 : ℝ := 2 * ((coarseA X.p S b i : ℝ) + X.k) / X.p with hc1
  set c2 : ℝ := 2 * X.La C0 * (S.A0 X.p : ℝ) / X.k with hc2
  have hc10 : 0 ≤ c1 := by rw [hc1]; positivity
  have hc20 : 0 ≤ c2 := by
    have := h.La1
    have : (0 : ℝ) ≤ (S.A0 X.p : ℝ) := by linarith
    rw [hc2]; positivity
  have hterm : ∀ l : Fin (segS X.TT j),
      ((if l.val < i.val + 1 then ((coarseA X.p S b l : ℤ) + (b.sg l : ℤ)) else 0 : ℤ) : ℝ) ≤
        (if l = i then (coarseA X.p S b i : ℝ) else 0) + (c1 + c2) := by
    intro l
    by_cases hl : l.val < i.val + 1
    · rw [if_pos hl]
      have hlσ : l.val < S.sigma := by omega
      have hsg : (b.sg l : ℝ) ≤ c2 := (hSt l hlσ).2.2.2.2
      push_cast
      by_cases hli : l = i
      · rw [if_pos hli, hli]
        rw [hli] at hsg
        linarith
      · rw [if_neg hli]
        have hlt : l < i := by
          rcases lt_or_eq_of_le (Nat.lt_succ_iff.1 hl) with h' | h'
          · exact h'
          · exact absurd (Fin.ext h') hli
        have hdl := dist_strictMono X.TT j hlt
        have hdi := (dist_pos_lt X.TT j i).2
        have hPP : X.p * X.p ^ (segG X.TT j - (segDists X.TT j).get i) ≤
            X.p ^ (segG X.TT j - (segDists X.TT j).get l) := by
          rw [← pow_succ']
          exact Nat.pow_le_pow_right (by have := h.p5; omega) (by omega)
        have hPP' : (X.p : ℝ) * ((X.p ^ (segG X.TT j - (segDists X.TT j).get i) : ℕ) : ℝ) ≤
            ((X.p ^ (segG X.TT j - (segDists X.TT j).get l) : ℕ) : ℝ) := by exact_mod_cast hPP
        have := coarse_ratio_small (k := X.k) (Nat.cast_nonneg _) h.bpos h.be0 hbe12 (h.levels j i).1 hp0 hPP' (hcb l).1
          (h.winB _ (pos_mem X.TT j l).1).2 (hcb i).2 (h.winB _ (pos_mem X.TT j i).1).1
        linarith
    · rw [if_neg hl]
      push_cast
      split_ifs
      · have : (0 : ℝ) ≤ (coarseA X.p S b i : ℝ) := Nat.cast_nonneg _
        linarith
      · linarith
  have hsumR : ((∑ l : Fin (segS X.TT j),
      (if l.val < i.val + 1 then ((coarseA X.p S b l : ℤ) + (b.sg l : ℤ)) else 0) : ℤ) : ℝ) ≤ (S.A0 X.p : ℝ) := by
    rw [Int.cast_sum]
    refine le_trans (Finset.sum_le_sum fun l _ => hterm l) ?_
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ i, if_pos (Finset.mem_univ i), Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hsN : ((segS X.TT j : ℕ) : ℝ) ≤ X.N1 := by exact_mod_cast (h.segB j).2
    have hpk : X.k ^ 2 ≤ (X.p : ℝ) := by
      have h1 := h.pk
      have h2 := h.Y1
      have : X.k ^ 2 * 1 ≤ X.k ^ 2 * X.Y ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
      linarith
    exact Ai_add_mul_le_A0 (ε := eps X C0) (Nat.cast_nonneg _) hAi hde h.de6 rfl hk5 hA0k hpk h.La1 h.one_le_level_alt (Nat.cast_nonneg _) hsN
  have hsumZ : (∑ l : Fin (segS X.TT j),
      (if l.val < i.val + 1 then ((coarseA X.p S b l : ℤ) + (b.sg l : ℤ)) else 0)) ≤ S.A0 X.p := by
    exact_mod_cast hsumR

  unfold cap
  have hcmp : ∀ l : Fin (segS X.TT j),
      (if l.val < i.val + 1 then (b.w l : ℤ) else 0) ≤
        (if l.val < i.val + 1 then ((coarseA X.p S b l : ℤ) + (b.sg l : ℤ)) else 0) * 0 +
        ((if (l : ℕ) < n then ((coarseA X.p S b l : ℤ) - (oEff S b l : ℤ)) else 0) +
          (if l.val < i.val + 1 then ((coarseA X.p S b l : ℤ) + (b.sg l : ℤ)) else 0)) := by
    intro l
    by_cases hl : l.val < i.val + 1
    · have hlσ : l.val < S.sigma := by omega
      have hw : (b.w l : ℤ) ≤ (coarseA X.p S b l : ℤ) := by exact_mod_cast (hSt l hlσ).2.1
      have hsg0 : (0 : ℤ) ≤ (b.sg l : ℤ) := Int.natCast_nonneg _
      have ho : (oEff S b l : ℤ) = (b.w l : ℤ) + (b.sg l : ℤ) := by
        unfold oEff
        rw [if_pos hlσ]
        push_cast
        ring
      rw [if_pos hl, if_pos hl]
      split_ifs
      · rw [ho]; linarith
      · linarith
    · have hln : ¬ (l : ℕ) < n := by omega
      rw [if_neg hl, if_neg hl, if_neg hln]
      simp
  have hs := Finset.sum_le_sum (s := Finset.univ) fun l _ => hcmp l
  simp only [mul_zero, zero_add] at hs
  rw [Finset.sum_add_distrib] at hs
  linarith

theorem top_rows_bound_holds : LeadingRowsBeyondThreshold :=
  TransportedAlt.of_explicit (fun _ => 1) (fun _ _ => 1) (fun Cc _ CE1 CE2 _ => T2 CE1 CE2 Cc 1)
    fun _ _ _ _ _ _ _ _ _ _ hCc hC0 _ h1 h2 _ _ _ _ _ _ _ _ _ t1 t2 t3 t4 t5 => by
      intro X _ hD hI hc j b hK i hi
      have hs := std_of hCc hC0 h1 h2 le_rfl t1 t2 t3 t4 t5 hD hI hc
      exact ⟨partial_width_le_cap le_rfl hs j b hK i hi i.val (by omega), partial_width_le_cap le_rfl hs j b hK i hi (i.val + 1) le_rfl⟩

end Formalism.MainNotions.ColumnSystems.Pf
