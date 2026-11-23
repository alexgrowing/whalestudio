import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.ColNumDef
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.FirstCoefficientFacts
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.PolyUpperBoundDelta

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf.GenusGluing

open Formalism.MainNotions.G

theorem column_first_coefficient_bound {a b' E0 Q Qj k N Y c N1 eps A0 : ℝ} (ha : 0 < a) (hQj0 : 0 < Qj) (hQ : Qj ≤ Q)
    (hN5 : E0 / a + Q / a ≤ eps) (hA0 : (a - E0) / Qj - 1 < A0) (hkb : k * b' ≤ a)
    (hHc : 1 * k ^ 3 * N * Q ^ 4 * c * Y ≤ b') (hN2 : 2 ≤ N) (hY1 : 1 ≤ Y) (heps2 : eps ≤ 1 / 2)
    (hepsk : 1 / k ≤ eps) (hk5 : 5 ≤ k) (hQ1 : 1 ≤ Q) (sq_level_le_degree : 2 * N1 + 3 ≤ k) (hN1 : 1 ≤ N1) (hc0 : 0 ≤ c) :
    0 < A0 ∧ 12 * c + 13 * k * N1 ^ 2 * Q * c ≤ 4 * (eps * A0) := by
  have hk0 : 0 < k := by linarith
  have hQ0 : 0 < Q := by linarith
  have e1 : E0 + Q ≤ eps * a := by
    rw [← add_div, div_le_iff₀ ha] at hN5; exact hN5
  have h5 : a * (1 - eps) < A0 * Qj := by
    have e2 : (a - E0) / Qj - 1 = (a - E0 - Qj) / Qj := by field_simp
    rw [e2, div_lt_iff₀ hQj0] at hA0
    linarith
  have h7 : a * (1 / 2) ≤ a * (1 - eps) := mul_le_mul_of_nonneg_left (by linarith) ha.le
  have hpos : 0 < A0 * Qj := by linarith
  have hA0p : 0 < A0 := (mul_pos_iff_of_pos_right hQj0).1 hpos
  have h6 : A0 * Qj ≤ A0 * Q := mul_le_mul_of_nonneg_left hQ hA0p.le
  have hb2 : 2 * (k ^ 3 * Q ^ 4 * c) ≤ b' := by
    have a5 : 0 ≤ k ^ 3 * Q ^ 4 * c := by positivity
    have a2 : 2 * (k ^ 3 * Q ^ 4 * c) ≤ N * (k ^ 3 * Q ^ 4 * c) := mul_le_mul_of_nonneg_right hN2 a5
    have a6 : 0 ≤ N * (k ^ 3 * Q ^ 4 * c) := by positivity
    have a3 : N * (k ^ 3 * Q ^ 4 * c) * 1 ≤ N * (k ^ 3 * Q ^ 4 * c) * Y := mul_le_mul_of_nonneg_left hY1 a6
    have a4 : 1 * k ^ 3 * N * Q ^ 4 * c * Y = N * (k ^ 3 * Q ^ 4 * c) * Y := by ring
    linarith
  have h8 : k * (2 * (k ^ 3 * Q ^ 4 * c)) ≤ k * b' := mul_le_mul_of_nonneg_left hb2 hk0.le
  have h9 : (k ^ 4 * Q ^ 3 * c) * Q < A0 * Q := by
    have e : (k ^ 4 * Q ^ 3 * c) * Q = k * (2 * (k ^ 3 * Q ^ 4 * c)) * (1 / 2) := by ring
    rw [e]
    linarith
  have h10 : k ^ 4 * Q ^ 3 * c < A0 := lt_of_mul_lt_mul_right h9 hQ0.le
  have h11 : 1 / k * A0 ≤ eps * A0 := mul_le_mul_of_nonneg_right hepsk hA0p.le
  have h12 : 1 / k * (k ^ 4 * Q ^ 3 * c) ≤ 1 / k * A0 := mul_le_mul_of_nonneg_left h10.le (by positivity)
  have h13 : 1 / k * (k ^ 4 * Q ^ 3 * c) = k ^ 3 * Q ^ 3 * c := by field_simp
  have hQ3 : Q ≤ Q ^ 3 := by
    calc Q = Q ^ 1 := (pow_one _).symm
      _ ≤ Q ^ 3 := pow_le_pow_right₀ hQ1 (by norm_num)
  have hkc : 0 ≤ k ^ 3 * c := by positivity
  have h14 : k ^ 3 * c * Q ≤ k ^ 3 * c * Q ^ 3 := mul_le_mul_of_nonneg_left hQ3 hkc
  have h15 : k ^ 3 * c * 1 ≤ k ^ 3 * c * Q := mul_le_mul_of_nonneg_left hQ1 hkc
  have hk3 : (125 : ℝ) ≤ k ^ 3 := by
    calc (125 : ℝ) = 5 ^ 3 := by norm_num
      _ ≤ k ^ 3 := pow_le_pow_left₀ (by norm_num) hk5 3
  have h16 : 125 * c ≤ k ^ 3 * c := mul_le_mul_of_nonneg_right hk3 hc0
  have hN12 : N1 ^ 2 ≤ (k / 2) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hkQc : 0 ≤ k * Q * c := by positivity
  have h17 : N1 ^ 2 * (k * Q * c) ≤ (k / 2) ^ 2 * (k * Q * c) := mul_le_mul_of_nonneg_right hN12 hkQc
  have e3 : 13 * k * N1 ^ 2 * Q * c = 13 * (N1 ^ 2 * (k * Q * c)) := by ring
  have e4 : (k / 2) ^ 2 * (k * Q * c) = (k ^ 3 * c * Q) / 4 := by ring
  have e5 : k ^ 3 * Q ^ 3 * c = k ^ 3 * c * Q ^ 3 := by ring
  refine ⟨hA0p, ?_⟩
  rw [e3]
  linarith

theorem column_margin_bound {mm n c ka N1 k Q : ℝ} (hmm : mm ≤ 12 * c) (hn0 : 0 ≤ n) (hN1 : 1 ≤ N1) (hka0 : 0 ≤ ka)
    (hka : ka = 13 * k * N1 * Q) :
    (mm + n * ka) + N1 * ((c - n) * ka) ≤ 12 * c + 13 * k * N1 ^ 2 * Q * c := by
  have h1 : n * ka * 1 ≤ n * ka * N1 := mul_le_mul_of_nonneg_left hN1 (mul_nonneg hn0 hka0)
  have e : 13 * k * N1 ^ 2 * Q * c = N1 * c * ka := by rw [hka]; ring
  rw [e]
  nlinarith

theorem column_lower_ratio {b' gl gi Al Ai Pl Pi p k Q be : ℝ} (hb : 0 < b') (hPi : 0 < Pi) (hk0 : 0 ≤ k)
    (hAl0 : 0 ≤ Al) (hl : Al * Pl ≤ gl) (hgl : gl ≤ b' * (1 + be)) (hP : p * Pi ≤ Pl)
    (hi : gi - k * Pi < Ai * Pi) (hgi : b' * (1 - be) ≤ gi) (hbe : be ≤ 1 / 12) (hPQ : Pi ≤ Q)
    (hkQ : 2 * (k * Q) ≤ b') : Al * p ≤ 3 * Ai := by
  have h1 : Al * (p * Pi) ≤ Al * Pl := mul_le_mul_of_nonneg_left hP hAl0
  have h2 : b' * (1 + be) ≤ b' * (13 / 12) := mul_le_mul_of_nonneg_left (by linarith) hb.le
  have h3 : b' * (11 / 12) ≤ b' * (1 - be) := mul_le_mul_of_nonneg_left (by linarith) hb.le
  have h4 : k * Pi ≤ k * Q := mul_le_mul_of_nonneg_left hPQ hk0
  have h5 : b' * (5 / 12) < Ai * Pi := by linarith
  have h6 : Al * p * Pi ≤ 3 * Ai * Pi := by
    have e : Al * p * Pi = Al * (p * Pi) := by ring
    have e' : 3 * Ai * Pi = 3 * (Ai * Pi) := by ring
    rw [e, e']
    linarith
  exact le_of_mul_le_mul_right h6 hPi

theorem column_first_goal {S mu NE eps A0 B : ℝ} (hS : S ≤ 2 * (eps * A0) + NE) (hmu : mu + NE ≤ B) (hB : B ≤ 4 * (eps * A0))
    (heps : eps ≤ 1 / 240) (hA0 : 0 ≤ A0) : S + mu ≤ A0 := by
  have h1 : eps * A0 ≤ 1 / 240 * A0 := mul_le_mul_of_nonneg_right heps hA0
  linarith

theorem column_second_goal {W S mu NE eps de A0 Ai B T N1 p : ℝ} (hW : W ≤ Ai + N1 * T) (hT : T * p = 3 * Ai)
    (hp0 : 0 < p) (hN1p : 3 * N1 ≤ eps * p) (hAi0 : 0 ≤ Ai)
    (hS : S ≤ 2 * (eps * A0) + NE) (hmu : mu + NE ≤ B) (hB : B ≤ 4 * (eps * A0)) (heps0 : 0 ≤ eps)
    (h40 : 40 * eps ≤ de) (hde6 : de < 1 / 6) (hA0 : 0 ≤ A0) (hdich : Ai * (1 + de) < A0) : W + S + mu ≤ A0 := by
  have hde0 : 0 ≤ de := by linarith
  have h1 : N1 * T ≤ eps * Ai := by
    have a1 : N1 * T * p ≤ eps * Ai * p := by
      have e : N1 * T * p = 3 * N1 * Ai := by
        calc N1 * T * p = N1 * (T * p) := by ring
          _ = 3 * N1 * Ai := by rw [hT]; ring
      have a2 : 3 * N1 * Ai ≤ eps * p * Ai := mul_le_mul_of_nonneg_right hN1p hAi0
      rw [e]
      linarith
    exact le_of_mul_le_mul_right a1 hp0
  have h2 : Ai * (1 + de) * (1 + eps) ≤ A0 * (1 + eps) := mul_le_mul_of_nonneg_right hdich.le (by linarith)
  have h3 : 0 ≤ eps * A0 := mul_nonneg heps0 hA0
  have h4 : eps * A0 * de ≤ eps * A0 * (1 / 6) := mul_le_mul_of_nonneg_left hde6.le h3
  have h5 : 40 * eps * A0 ≤ de * A0 := mul_le_mul_of_nonneg_right h40 hA0
  have h6 : (Ai * (1 + eps) + 6 * (eps * A0)) * (1 + de) ≤ A0 * (1 + de) := by
    have e : (Ai * (1 + eps) + 6 * (eps * A0)) * (1 + de) =
        Ai * (1 + de) * (1 + eps) + 6 * (eps * A0) + 6 * (eps * A0 * de) := by ring
    rw [e]
    linarith
  have h7 : Ai * (1 + eps) + 6 * (eps * A0) ≤ A0 := le_of_mul_le_mul_right h6 (by linarith)
  linarith

theorem column_partial_sum_S {s : ℕ} (σ : ℕ) (sg : Fin s → ℝ) {B N1 : ℝ} (hB : 0 ≤ B) (hs : (s : ℝ) ≤ N1)
    (h : ∀ l : Fin s, (l : ℕ) < σ → sg l ≤ B) :
    (∑ l : Fin s, (if (l : ℕ) < σ then sg l else 0)) ≤ N1 * B := by
  calc (∑ l : Fin s, (if (l : ℕ) < σ then sg l else 0)) ≤ ∑ _l : Fin s, B := by
        apply Finset.sum_le_sum
        intro l _
        split_ifs with hl
        · exact h l hl
        · exact hB
    _ = (s : ℝ) * B := by simp
    _ ≤ N1 * B := mul_le_mul_of_nonneg_right hs hB

theorem column_partial_sum_W {s : ℕ} (i : Fin s) (w : Fin s → ℝ) {Ai T N1 : ℝ} (hT : 0 ≤ T) (hs : (s : ℝ) ≤ N1)
    (hi : w i ≤ Ai) (hl : ∀ l : Fin s, (l : ℕ) < (i : ℕ) → w l ≤ T) :
    (∑ l : Fin s, (if (l : ℕ) ≤ (i : ℕ) then w l else 0)) ≤ Ai + N1 * T := by
  calc (∑ l : Fin s, (if (l : ℕ) ≤ (i : ℕ) then w l else 0))
      ≤ ∑ l : Fin s, ((if l = i then Ai else 0) + T) := by
        apply Finset.sum_le_sum
        intro l _
        by_cases h1 : l = i
        · subst h1
          simp only [le_refl, if_true]
          linarith
        · rw [if_neg h1]
          split_ifs with h2
          · have : (l : ℕ) < (i : ℕ) := lt_of_le_of_ne h2 (fun h => h1 (Fin.ext h))
            linarith [hl l this]
          · linarith
    _ = Ai + (s : ℝ) * T := by
        rw [Finset.sum_add_distrib]
        simp
    _ ≤ Ai + N1 * T := by
        have := mul_le_mul_of_nonneg_right hs hT
        linarith

theorem three_level_le_eps_prime {C0 Cde CE1 CE2 : ℝ} {X : Loc} (St : Std C0 Cde CE1 CE2 1 X) :
    3 * (X.N1 : ℝ) ≤ eps X C0 * X.p := by
  have hk5 := St.k5
  have hk0 : 0 < X.k := by linarith
  have hN1r := St.one_le_level_alt
  have heps0 := St.eps0
  have a1 : (X.N1 : ℝ) ≤ eps X C0 * X.k := by
    have e : eps X C0 * X.k = X.N1 * X.La C0 := by
      unfold eps
      field_simp
    rw [e]
    have := mul_le_mul_of_nonneg_left St.La1 (by linarith : (0 : ℝ) ≤ (X.N1 : ℝ))
    linarith
  have a2 : X.k ^ 2 ≤ (X.p : ℝ) := by
    have h3 := St.pk
    have h4 := St.Y1
    have h7 : X.k ^ 2 * 1 ≤ X.k ^ 2 * X.Y ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
    linarith
  have a3 : eps X C0 * X.k ^ 2 ≤ eps X C0 * X.p := mul_le_mul_of_nonneg_left a2 heps0
  have a4 : (X.N1 : ℝ) * X.k ≤ eps X C0 * X.k * X.k := mul_le_mul_of_nonneg_right a1 hk0.le
  have a5 : (X.N1 : ℝ) * 5 ≤ (X.N1 : ℝ) * X.k := mul_le_mul_of_nonneg_left hk5 (by linarith)
  have e2 : eps X C0 * X.k * X.k = eps X C0 * X.k ^ 2 := by ring
  linarith

theorem m1num_of_std {C0 Cde CE1 CE2 : ℝ} {X : Loc} (St : Std C0 Cde CE1 CE2 1 X) (mm : ℝ)
    (hmm : mm = 0 ∨ mm = 12 * (X.c : ℝ)) (n : ℕ) (_hn1 : 1 ≤ n) (hnc : n ≤ X.c)
    (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m)
    (hb : BLk C0 Cde CE1 CE2 X (((X.c - n : ℕ) : ℝ) * ka1 X) j b) :
    (∑ l : Fin (segS X.TT j), (if (l : ℕ) < (X.seg C0 CE1 CE2 j).sigma then (b.sg l : ℤ) else 0)) ≤
        ⌊(((X.seg C0 CE1 CE2 j).A0 X.p : ℤ) : ℝ) - (mm + (n : ℝ) * ka1 X)⌋ ∧
    ∀ i : Fin (segS X.TT j), (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma →
      (∑ l : Fin (segS X.TT j), (if (l : ℕ) ≤ (i : ℕ) then (b.w l : ℤ) else 0)) +
        (∑ l : Fin (segS X.TT j), (if (l : ℕ) < (X.seg C0 CE1 CE2 j).sigma then (b.sg l : ℤ) else 0)) ≤
        ⌊(((X.seg C0 CE1 CE2 j).A0 X.p : ℤ) : ℝ) - (mm + (n : ℝ) * ka1 X)⌋ := by
  obtain ⟨hdig, -, hS, -, -⟩ := hb
  have H := segHyp_of St j
  have hk5 := St.k5
  have hk0 : 0 < X.k := by linarith
  have hp0 : (0 : ℝ) < X.p := by linarith [St.p1]
  have hN1r := St.one_le_level_alt
  have hQ1 := St.Q1
  have heps0 := St.eps0
  have h40 := St.forty_epsilon_le_delta
  have hde6 := St.de6
  have heps240 : eps X C0 ≤ 1 / 240 := by linarith
  have hc0 : (0 : ℝ) ≤ (X.c : ℝ) := Nat.cast_nonneg _
  have hQj0 : (0 : ℝ) < ((X.p ^ segG X.TT j : ℕ) : ℝ) := by
    push_cast
    exact pow_pos hp0 _
  have hQjQ : ((X.p ^ segG X.TT j : ℕ) : ℝ) ≤ X.Q := by
    push_cast
    exact H.Q
  have hA0lt : ((X.a : ℝ) - X.E0 C0 CE1 CE2) / ((X.p ^ segG X.TT j : ℕ) : ℝ) - 1 <
      (((X.seg C0 CE1 CE2 j).A0 X.p : ℤ) : ℝ) := Int.sub_one_lt_floor _
  obtain ⟨hA0p, hB⟩ := column_first_coefficient_bound (eps := eps X C0) St.apos hQj0 hQjQ St.N5 hA0lt St.kb St.Hc St.N2 St.Y1 (by linarith) St.eps_ge hk5 hQ1
    St.N1k hN1r hc0
  have hka0 : 0 ≤ ka1 X := by
    unfold ka1
    positivity
  have hmm' : mm ≤ 12 * (X.c : ℝ) := by
    rcases hmm with h | h
    · rw [h]; positivity
    · exact h.le
  have hcast : (((X.c - n : ℕ) : ℕ) : ℝ) = (X.c : ℝ) - (n : ℝ) := Nat.cast_sub hnc
  have hmu := column_margin_bound (c := (X.c : ℝ)) (k := X.k) (Q := X.Q) hmm' (Nat.cast_nonneg n) hN1r hka0 rfl
  have hE0 : 0 ≤ ((X.c : ℝ) - (n : ℝ)) * ka1 X := by
    rw [← hcast]
    positivity
  have hs : ((segS X.TT j : ℕ) : ℝ) ≤ (X.N1 : ℝ) := by exact_mod_cast (St.segB j).2
  have hLa0 : 0 ≤ X.La C0 := by linarith [St.La1]
  generalize hA0def : (((X.seg C0 CE1 CE2 j).A0 X.p : ℤ) : ℝ) = A0 at *
  have hBd0 : 0 ≤ 2 * X.La C0 * A0 / X.k + ((X.c : ℝ) - (n : ℝ)) * ka1 X := by
    have : 0 ≤ 2 * X.La C0 * A0 / X.k := by positivity
    linarith
  have hsumS : (∑ l : Fin (segS X.TT j), (if (l : ℕ) < (X.seg C0 CE1 CE2 j).sigma then (b.sg l : ℝ) else 0)) ≤
      2 * (eps X C0 * A0) + (X.N1 : ℝ) * (((X.c : ℝ) - (n : ℝ)) * ka1 X) := by
    have h1 := column_partial_sum_S (X.seg C0 CE1 CE2 j).sigma (fun l => (b.sg l : ℝ)) hBd0 hs
      (fun l hl => by
        have := (hS l hl).2.2.2
        rw [hcast] at this
        exact this)
    have e : (X.N1 : ℝ) * (2 * X.La C0 * A0 / X.k + ((X.c : ℝ) - (n : ℝ)) * ka1 X) =
        2 * (eps X C0 * A0) + (X.N1 : ℝ) * (((X.c : ℝ) - (n : ℝ)) * ka1 X) := by
      unfold eps
      ring
    rw [e] at h1
    exact h1
  constructor
  · rw [Int.le_floor]
    push_cast
    have := column_first_goal hsumS hmu hB heps240 hA0p.le
    linarith
  · intro i hi
    rw [Int.le_floor]
    push_cast
    obtain ⟨hP0, -, -, hQ, hPQ⟩ := St.levels j i
    have hcbi := coarse_bounds (X.bT (segPos X.TT j i)) (X.p ^ (segG X.TT j - (segDists X.TT j).get i)) (b.rz i)
      (fun c => (hdig.1 i c).1) (hdig.2.1 i).1 (hdig.2.1 i).2
    have hAPi : (X.bT (segPos X.TT j i) : ℝ) - X.k * ((X.p ^ (segG X.TT j - (segDists X.TT j).get i) : ℕ) : ℝ) <
        (coarseA X.p (X.seg C0 CE1 CE2 j) b i : ℝ) * ((X.p ^ (segG X.TT j - (segDists X.TT j).get i) : ℕ) : ℝ) :=
      hcbi.2
    have hbTi : X.b' * (1 - _root_.Formalism.MainNotions.ColumnSystems.Pf.be X C0) ≤ (X.bT (segPos X.TT j i) : ℝ) := (H.bT i).1
    have hbe12 : _root_.Formalism.MainNotions.ColumnSystems.Pf.be X C0 ≤ 1 / 12 := by linarith [St.be18]
    have hdich : (coarseA X.p (X.seg C0 CE1 CE2 j) b i : ℝ) * (1 + X.de C0 Cde) < A0 := by
      rw [← hA0def]
      exact (coarse_degree_alternative le_rfl St j b hdig i).1 hi
    have hAi0 : (0 : ℝ) ≤ (coarseA X.p (X.seg C0 CE1 CE2 j) b i : ℝ) := Nat.cast_nonneg _
    have hlow : ∀ l : Fin (segS X.TT j), (l : ℕ) < (i : ℕ) →
        (b.w l : ℝ) ≤ 3 * (coarseA X.p (X.seg C0 CE1 CE2 j) b i : ℝ) / X.p := by
      intro l hl
      have hcbl := coarse_bounds (X.bT (segPos X.TT j l)) (X.p ^ (segG X.TT j - (segDists X.TT j).get l)) (b.rz l)
        (fun c => (hdig.1 l c).1) (hdig.2.1 l).1 (hdig.2.1 l).2
      have hAPl : (coarseA X.p (X.seg C0 CE1 CE2 j) b l : ℝ) *
          ((X.p ^ (segG X.TT j - (segDists X.TT j).get l) : ℕ) : ℝ) ≤ (X.bT (segPos X.TT j l) : ℝ) := hcbl.1
      have hbTl : (X.bT (segPos X.TT j l) : ℝ) ≤ X.b' * (1 + _root_.Formalism.MainNotions.ColumnSystems.Pf.be X C0) := (H.bT l).2
      have hd1 : (segDists X.TT j).get l < (segDists X.TT j).get i := H.dmono (Fin.lt_def.mpr hl)
      have hd2 : (segDists X.TT j).get i < segG X.TT j := (dist_pos_lt X.TT j i).2
      have hPP : (X.p : ℝ) * ((X.p ^ (segG X.TT j - (segDists X.TT j).get i) : ℕ) : ℝ) ≤
          ((X.p ^ (segG X.TT j - (segDists X.TT j).get l) : ℕ) : ℝ) := by
        have hn : X.p * X.p ^ (segG X.TT j - (segDists X.TT j).get i) ≤
            X.p ^ (segG X.TT j - (segDists X.TT j).get l) := by
          rw [← pow_succ']
          exact Nat.pow_le_pow_right (by have := St.p5; omega) (by omega)
        exact_mod_cast hn
      have h3 := column_lower_ratio St.bpos hP0 hk0.le (Nat.cast_nonneg _) hAPl hbTl hPP hAPi hbTi hbe12 (hPQ.trans hQ)
        (St.two_rank_mul_Q_le le_rfl)
      have hw : (b.w l : ℝ) ≤ (coarseA X.p (X.seg C0 CE1 CE2 j) b l : ℝ) := by
        exact_mod_cast (hS l (lt_trans hl hi)).2.1
      rw [le_div_iff₀ hp0]
      have := mul_le_mul_of_nonneg_right hw hp0.le
      linarith
    have hwi : (b.w i : ℝ) ≤ (coarseA X.p (X.seg C0 CE1 CE2 j) b i : ℝ) := by
      exact_mod_cast (hS i hi).2.1
    have hsumW := column_partial_sum_W i (fun l => (b.w l : ℝ)) (by positivity) hs hwi hlow
    have hN1p := three_level_le_eps_prime St
    have hT : 3 * (coarseA X.p (X.seg C0 CE1 CE2 j) b i : ℝ) / X.p * X.p =
        3 * (coarseA X.p (X.seg C0 CE1 CE2 j) b i : ℝ) := div_mul_cancel₀ _ hp0.ne'
    have := column_second_goal hsumW hT hp0 hN1p hAi0 hsumS hmu hB heps0 h40 hde6 hA0p.le hdich
    linarith

theorem column_numerics_holds : ColumnNumericsBeyond :=
  TransportedAlt.mono (fun _ _ _ _ _ _ _ _ _ _ h X hD hH hc mm hmm n hn1 hnc j b hb =>
    m1num_of_std (h X hD hH hc) mm hmm n hn1 hnc j b hb) threshold_standard_one

end Formalism.MainNotions.ColumnSystems.Pf.GenusGluing
