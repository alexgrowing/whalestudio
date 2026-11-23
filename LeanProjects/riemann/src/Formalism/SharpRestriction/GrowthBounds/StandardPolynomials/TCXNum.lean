import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.TCNumDef
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.PolyUpperBoundDelta
set_option maxHeartbeats 4000000

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

theorem tcx_roomR {b' g A P Q k c de be eps N Y N1 ka : ℝ} (hb : 0 < b') (hAP : g - k * P < A * P)
    (hbT : b' * (1 - be) ≤ g) (hbe : be ≤ de / 2 - 18 * eps) (heps : 0 ≤ eps) (hde6 : de < 1 / 6)
    (hde40 : 40 * eps ≤ de) (hepsk : 1 / k ≤ eps) (hk5 : 5 ≤ k) (hQ1 : 1 ≤ Q) (hP0 : 0 < P) (hPQ : P ≤ Q)
    (sq_level_le_degree : 2 * N1 + 3 ≤ k) (hN2 : 2 ≤ N) (hY1 : 1 ≤ Y) (hHc : 1 * k ^ 3 * N * Q ^ 4 * c * Y ≤ b')
    (hc1 : 1 ≤ c) (hA0 : 0 ≤ A) (hN10 : 0 ≤ N1) (hka : ka = 13 * k * N1 * Q) :
    c * (ka + 2 * Q + 3 * k) + 4 ≤ de / 4 * A := by
  have hk0 : 0 < k := by linarith
  have hQ0 : 0 < Q := by linarith
  have hbe12 : be ≤ 1 / 12 := by linarith
  have h1 : b' * (11 / 12) ≤ b' * (1 - be) := mul_le_mul_of_nonneg_left (by linarith) hb.le
  have h2 : A * P ≤ A * Q := mul_le_mul_of_nonneg_left hPQ hA0
  have h3 : k * P ≤ k * Q := mul_le_mul_of_nonneg_left hPQ hk0.le
  have hAQ : b' * (11 / 12) - k * Q ≤ A * Q := by linarith
  have hQ2 : Q ^ 2 ≤ Q ^ 4 := pow_le_pow_right₀ hQ1 (by norm_num)
  have hk3 : 0 ≤ k ^ 3 := by positivity
  have hb2 : 2 * k ^ 3 * Q ^ 2 * c ≤ b' := by
    have a0 : 0 ≤ k ^ 3 * c := by positivity
    have a1 : 2 * k ^ 3 * Q ^ 2 * c ≤ 2 * k ^ 3 * Q ^ 4 * c := by
      have := mul_le_mul_of_nonneg_left hQ2 a0
      linarith
    have a5 : 0 ≤ k ^ 3 * Q ^ 4 * c := by positivity
    have a2 : 2 * (k ^ 3 * Q ^ 4 * c) ≤ N * (k ^ 3 * Q ^ 4 * c) := mul_le_mul_of_nonneg_right hN2 a5
    have a6 : 0 ≤ N * (k ^ 3 * Q ^ 4 * c) := by positivity
    have a3 : N * (k ^ 3 * Q ^ 4 * c) * 1 ≤ N * (k ^ 3 * Q ^ 4 * c) * Y := mul_le_mul_of_nonneg_left hY1 a6
    have a4 : 1 * k ^ 3 * N * Q ^ 4 * c * Y = N * (k ^ 3 * Q ^ 4 * c) * Y := by ring
    linarith
  have hA1 : ((11 / 6) * k ^ 3 * Q * c - k) * Q ≤ A * Q := by
    have e : ((11 / 6) * k ^ 3 * Q * c - k) * Q = (11 / 12) * (2 * k ^ 3 * Q ^ 2 * c) - k * Q := by ring
    rw [e]
    linarith
  have hA2 : (11 / 6) * k ^ 3 * Q * c - k ≤ A := le_of_mul_le_mul_right hA1 hQ0
  have hdek : 40 ≤ de * k := by
    have a1 : 40 * (1 / k) ≤ de := by linarith
    have a2 : 40 * (1 / k) * k = 40 := by field_simp
    have a3 : 40 * (1 / k) * k ≤ de * k := mul_le_mul_of_nonneg_right a1 hk0.le
    linarith
  have hfin : ((55 / 3) * k ^ 2 * Q * c - 10) * k ≤ de / 4 * A * k := by
    have a1 : 40 * A ≤ de * k * A := mul_le_mul_of_nonneg_right hdek hA0
    have a2 : ((55 / 3) * k ^ 2 * Q * c - 10) * k = (10 / 1) * ((11 / 6) * k ^ 3 * Q * c - k) := by ring
    have a3 : de / 4 * A * k = (de * k * A) / 4 := by ring
    rw [a2, a3]
    linarith
  have hfin2 : (55 / 3) * k ^ 2 * Q * c - 10 ≤ de / 4 * A := le_of_mul_le_mul_right hfin hk0
  have hN1 : N1 ≤ k := by linarith
  have hkaB : ka ≤ 13 * k ^ 2 * Q := by
    rw [hka]
    have a1 : k * N1 ≤ k * k := mul_le_mul_of_nonneg_left hN1 hk0.le
    have a2 : k * N1 * Q ≤ k * k * Q := mul_le_mul_of_nonneg_right a1 hQ0.le
    have e1 : 13 * k * N1 * Q = 13 * (k * N1 * Q) := by ring
    have e2 : 13 * k ^ 2 * Q = 13 * (k * k * Q) := by ring
    rw [e1, e2]
    linarith
  have hkQ : k ≤ k * Q := le_mul_of_one_le_right hk0.le hQ1
  have hk25 : 5 * 5 ≤ k * k := mul_le_mul hk5 hk5 (by norm_num) hk0.le
  have hk5k : 5 * k ≤ k * k := mul_le_mul_of_nonneg_right hk5 hk0.le
  have hc0 : 0 ≤ c := by linarith
  have hQc0 : 0 ≤ Q * c := mul_nonneg hQ0.le hc0
  have hQc1 : 1 ≤ Q * c := one_le_mul_of_one_le_of_one_le hQ1 hc1
  have hQc : 25 * (Q * c) ≤ k * k * (Q * c) := by
    have := mul_le_mul_of_nonneg_right hk25 hQc0
    linarith
  have hkQc : 5 * k * (Q * c) ≤ k * k * (Q * c) := mul_le_mul_of_nonneg_right hk5k hQc0
  have hX : k ^ 2 * Q * c = k * k * (Q * c) := by ring
  have hfirst : c * (ka + 2 * Q + 3 * k) ≤ c * (13 * k ^ 2 * Q + 2 * Q + 3 * (k * Q)) := by
    apply mul_le_mul_of_nonneg_left _ hc0
    linarith
  have e1 : c * (13 * k ^ 2 * Q + 2 * Q + 3 * (k * Q)) =
      13 * (k * k * (Q * c)) + 2 * (Q * c) + 3 * (k * (Q * c)) := by ring
  have e2 : 55 / 3 * k ^ 2 * Q * c = 55 / 3 * (k * k * (Q * c)) := by ring
  have e3 : 5 * k * (Q * c) = 5 * (k * (Q * c)) := by ring
  rw [e1] at hfirst
  rw [e2] at hfin2
  rw [e3] at hkQc
  linarith

variable {C0 Cde CE1 CE2 : ℝ} {X : Loc}

theorem tcx_room (St : Std C0 Cde CE1 CE2 1 X) (hc : 1 ≤ X.c) (j : Fin (numSeg X.TT))
    (b : SegBlock (segS X.TT j) X.m) (hdig : DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b)
    (i : Fin (segS X.TT j)) :
    (X.c : ℝ) * (ka1 X + 2 * X.Q + 3 * X.k) + 4 ≤
      X.de C0 Cde / 4 * (coarseA X.p (X.seg C0 CE1 CE2 j) b i : ℝ) := by
  have H := segHyp_of St j
  obtain ⟨hP0, -, -, hQ, hPQ⟩ := St.levels j i
  have hcb := coarse_bounds (X.bT (segPos X.TT j i)) (X.p ^ (segG X.TT j - (segDists X.TT j).get i)) (b.rz i)
    (fun c => (hdig.1 i c).1) (hdig.2.1 i).1 (hdig.2.1 i).2
  have hAP : (X.bT (segPos X.TT j i) : ℝ) - X.k * ((X.p ^ (segG X.TT j - (segDists X.TT j).get i) : ℕ) : ℝ) <
      (coarseA X.p (X.seg C0 CE1 CE2 j) b i : ℝ) * ((X.p ^ (segG X.TT j - (segDists X.TT j).get i) : ℕ) : ℝ) := hcb.2
  have hbT : X.b' * (1 - _root_.Formalism.MainNotions.ColumnSystems.Pf.be X C0) ≤ (X.bT (segPos X.TT j i) : ℝ) := (H.bT i).1
  have hc1 : (1 : ℝ) ≤ (X.c : ℝ) := by exact_mod_cast hc
  exact tcx_roomR St.bpos hAP hbT St.be18 St.eps0 St.de6 St.forty_epsilon_le_delta St.eps_ge St.k5 St.Q1 hP0 (hPQ.trans hQ) St.N1k
    St.N2 St.Y1 St.Hc hc1 (Nat.cast_nonneg _) (Nat.cast_nonneg _) rfl

theorem tcx_floor {x y : ℝ} {z : ℤ} (h : x + z ≤ y) : ⌊x⌋ + z ≤ ⌊y⌋ := by
  apply Int.le_floor.2
  push_cast
  linarith [Int.floor_le x]

theorem tcx_capdiff (p : ℕ) {s r : ℕ} (S : SegData s) (b b' : SegBlock s r) (l : ℕ) (D : ℤ) (hD : 0 ≤ D)
    (h : ∀ i : Fin s, ((coarseA p S b i : ℤ) - (oEff S b i : ℤ)) - ((coarseA p S b' i : ℤ) - (oEff S b' i : ℤ)) ≤ D) :
    cap p S b l - cap p S b' l ≤ (s : ℤ) * D := by
  unfold cap
  have h2 : ∀ i ∈ (Finset.univ : Finset (Fin s)),
      (if (i : ℕ) < l then ((coarseA p S b i : ℤ) - (oEff S b i : ℤ)) else 0) -
        (if (i : ℕ) < l then ((coarseA p S b' i : ℤ) - (oEff S b' i : ℤ)) else 0) ≤ D := by
    intro i _
    split_ifs
    · exact h i
    · simpa using hD
  have h3 := Finset.sum_le_sum h2
  rw [Finset.sum_sub_distrib] at h3
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h3
  linarith

theorem tcx_termU {A A' o o' K q : ℕ} (hA : A ≤ A' + K) (ho : o' ≤ o + 2 * (K + q)) :
    ((A : ℤ) - (o : ℤ)) - ((A' : ℤ) - (o' : ℤ)) ≤ ((3 * K + 2 * q : ℕ) : ℤ) := by
  push_cast
  omega

theorem tcx_termS {A A' w w' g g' K q : ℕ} (hA : A ≤ A' + K) (hw : w' ≤ w + (K + q)) (hg : g' ≤ g + (K + q)) :
    ((A : ℤ) - ((w + g : ℕ) : ℤ)) - ((A' : ℤ) - ((w' + g' : ℕ) : ℤ)) ≤ ((3 * K + 2 * q : ℕ) : ℤ) := by
  push_cast
  omega

theorem numCore_of_std {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ}
    (hstd : ∀ X : Loc, D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X → Std C0 Cde CE1 CE2 1 X) :
    NumCoreAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  intro X hD hH hcB mm _ n hn1 hnc e he1 hen j b hb
  have St := hstd X hD hH hcB
  have hc : 1 ≤ X.c := le_trans hn1 hnc
  obtain ⟨hdig, hU, hS, _, hP2⟩ := hb
  have hk5 := St.k5
  have hQ1 := St.Q1
  have hN1pos : (1 : ℝ) ≤ X.N1 := by exact_mod_cast St.N1pos
  have hde0 : 0 ≤ X.de C0 Cde := le_trans (mul_nonneg (by norm_num) St.eps0) St.forty_epsilon_le_delta
  have hde6 := St.de6
  have he1r : (1 : ℝ) ≤ e := by exact_mod_cast he1
  have hecr : (e : ℝ) ≤ X.c := by exact_mod_cast (le_of_lt (lt_of_lt_of_le hen hnc))
  have hkdef : X.k = (X.m : ℝ) + 1 := rfl
  have hQdef : X.Q = (X.p : ℝ) ^ X.G' := rfl
  have hk0 : 0 < X.k := by linarith
  have hQ0 : 0 < X.Q := by linarith
  have hka : ka1 X = 13 * X.k * X.N1 * X.Q := rfl
  have hkapos : 0 ≤ ka1 X := by
    rw [hka]
    have : (0 : ℝ) ≤ X.N1 := by linarith
    positivity
  have hE : (((X.c - n : ℕ)) : ℝ) ≤ X.c := by exact_mod_cast Nat.sub_le _ _
  have hE' : (((X.c - (n - e) : ℕ)) : ℝ) * ka1 X = ((X.c - n : ℕ) : ℝ) * ka1 X + e * ka1 X := by
    have : X.c - (n - e) = (X.c - n) + e := by omega
    rw [this]
    push_cast
    ring
  have hne : (((n - e : ℕ)) : ℝ) = (n : ℝ) - e := Nat.cast_sub (le_of_lt hen)

  have hkQ1 : 1 ≤ X.k * X.Q := one_le_mul_of_one_le_of_one_le (by linarith) hQ1
  have hQe1 : 1 ≤ X.Q * e := one_le_mul_of_one_le_of_one_le hQ1 he1r
  have hx : e * ka1 X = 13 * (X.N1 * X.k * X.Q * e) := by rw [hka]; ring
  have hN0 : (0 : ℝ) ≤ X.N1 := by linarith
  have b1 : (X.N1 : ℝ) * e ≤ X.N1 * X.k * X.Q * e := by
    have := mul_le_mul_of_nonneg_left hkQ1 (mul_nonneg hN0 (by linarith : (0:ℝ) ≤ e))
    nlinarith
  have b2 : (X.N1 : ℝ) * X.k ≤ X.N1 * X.k * X.Q * e := by
    have := mul_le_mul_of_nonneg_left hQe1 (mul_nonneg hN0 hk0.le)
    nlinarith
  have b3 : (X.N1 : ℝ) * (X.Q * e) ≤ X.N1 * X.k * X.Q * e := by
    have h1k : (1 : ℝ) ≤ X.k := by linarith
    have := mul_le_mul_of_nonneg_left h1k (mul_nonneg hN0 (by linarith : (0:ℝ) ≤ X.Q * e))
    nlinarith
  have b4 : X.k ≤ (X.N1 : ℝ) * X.k := le_mul_of_one_le_left hk0.le hN1pos
  have b5 : X.Q * e ≤ (X.N1 : ℝ) * (X.Q * e) := le_mul_of_one_le_left (by linarith) hN1pos
  have hnumA : 3 * X.k + 2 * (X.Q * e) ≤ e * ka1 X := by rw [hx]; linarith
  have hnumB : (X.N1 : ℝ) * e + ((X.N1 : ℝ) + 1) * (X.k + X.Q * e) + (X.N1 : ℝ) * (3 * X.k + 2 * (X.Q * e)) ≤
      e * ka1 X := by
    have e1 : (X.N1 : ℝ) * e + ((X.N1 : ℝ) + 1) * (X.k + X.Q * e) + (X.N1 : ℝ) * (3 * X.k + 2 * (X.Q * e)) =
        (X.N1 : ℝ) * e + 4 * ((X.N1 : ℝ) * X.k) + 3 * ((X.N1 : ℝ) * (X.Q * e)) + X.k + X.Q * e := by ring
    rw [e1, hx]
    linarith
  refine ⟨?_, ?_⟩
  ·
    intro i hi
    obtain ⟨-, hoR, -, -⟩ := hU i hi
    have room := tcx_room St hc j b hdig i
    have hEk : (((X.c - n : ℕ)) : ℝ) * ka1 X ≤ X.c * ka1 X := mul_le_mul_of_nonneg_right hE hkapos
    have hQec : X.Q * e ≤ X.Q * X.c := mul_le_mul_of_nonneg_left hecr hQ0.le
    have hkc : 0 ≤ X.k * X.c := by positivity
    have goalR : ((1 + 2 * (X.p ^ X.G' * e) + b.o i : ℕ) : ℝ) ≤ (coarseA X.p (X.seg C0 CE1 CE2 j) b i : ℝ) := by
      push_cast
      rw [← hQdef]
      have e1 : (coarseA X.p (X.seg C0 CE1 CE2 j) b i : ℝ) * (1 - X.de C0 Cde / 4) =
          (coarseA X.p (X.seg C0 CE1 CE2 j) b i : ℝ) - X.de C0 Cde / 4 * (coarseA X.p (X.seg C0 CE1 CE2 j) b i : ℝ) := by
        ring
      have e2 : (X.c : ℝ) * (ka1 X + 2 * X.Q + 3 * X.k) = X.c * ka1 X + 2 * (X.Q * X.c) + 3 * (X.k * X.c) := by ring
      rw [e1] at hoR
      rw [e2] at room
      linarith
    exact_mod_cast goalR
  · intro b' hdig' hA hU' hS' hP1' hP2'
    refine ⟨⟨hdig', ?_, ?_, hP1', ?_⟩, ?_⟩
    · intro i hi
      obtain ⟨h1, h2, h3, h4⟩ := hU' i hi
      obtain ⟨-, hoR, -, -⟩ := hU i hi
      refine ⟨h1, ?_, h3, h4⟩
      have h2R : (b'.o i : ℝ) ≤ (b.o i : ℝ) + 2 * (X.k + X.Q * e) := by
        have := (Nat.cast_le (α := ℝ)).2 h2
        push_cast at this
        rw [hkdef, hQdef]
        linarith
      have hAR : (coarseA X.p (X.seg C0 CE1 CE2 j) b i : ℝ) ≤ (coarseA X.p (X.seg C0 CE1 CE2 j) b' i : ℝ) + X.k := by
        have := (Nat.cast_le (α := ℝ)).2 (hA i)
        push_cast at this
        rw [hkdef]
        linarith
      have hm : 0 ≤ 1 - X.de C0 Cde / 4 := by linarith
      have h5 := mul_le_mul_of_nonneg_right hAR hm
      have h6 : X.k * (1 - X.de C0 Cde / 4) ≤ X.k := by nlinarith
      rw [hE']
      have e1 : ((coarseA X.p (X.seg C0 CE1 CE2 j) b' i : ℝ) + X.k) * (1 - X.de C0 Cde / 4) =
          (coarseA X.p (X.seg C0 CE1 CE2 j) b' i : ℝ) * (1 - X.de C0 Cde / 4) + X.k * (1 - X.de C0 Cde / 4) := by ring
      rw [e1] at h5
      linarith
    · intro i hi
      obtain ⟨h1, h2, h3, h4, -⟩ := hS' i hi
      obtain ⟨-, -, -, hsR⟩ := hS i hi
      refine ⟨h1, h2, h3, ?_⟩
      have h4R : (b'.sg i : ℝ) ≤ (b.sg i : ℝ) + (X.k + X.Q * e) := by
        have := (Nat.cast_le (α := ℝ)).2 h4
        push_cast at this
        rw [hkdef, hQdef]
        linarith
      rw [hE']
      linarith
    · have hPR : (b'.oPlus : ℝ) ≤ (b.oPlus : ℝ) + X.Q * e := by
        have := (Nat.cast_le (α := ℝ)).2 hP2'
        push_cast at this
        rw [hQdef]
        linarith
      rw [hE']
      linarith
    · intro l V hV
      have hterm : ∀ i : Fin (segS X.TT j),
          ((coarseA X.p (X.seg C0 CE1 CE2 j) b i : ℤ) - (oEff (X.seg C0 CE1 CE2 j) b i : ℤ)) -
            ((coarseA X.p (X.seg C0 CE1 CE2 j) b' i : ℤ) - (oEff (X.seg C0 CE1 CE2 j) b' i : ℤ)) ≤
            ((3 * (X.m + 1) + 2 * (X.p ^ X.G' * e) : ℕ) : ℤ) := by
        intro i
        by_cases hi : (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma
        · have e1 : oEff (X.seg C0 CE1 CE2 j) b i = b.w i + b.sg i := if_pos hi
          have e2 : oEff (X.seg C0 CE1 CE2 j) b' i = b'.w i + b'.sg i := if_pos hi
          rw [e1, e2]
          obtain ⟨-, -, -, hg, hw⟩ := hS' i hi
          exact tcx_termS (hA i) hw hg
        · have e1 : oEff (X.seg C0 CE1 CE2 j) b i = b.o i := if_neg hi
          have e2 : oEff (X.seg C0 CE1 CE2 j) b' i = b'.o i := if_neg hi
          rw [e1, e2]
          obtain ⟨-, ho, -, -⟩ := hU' i (not_lt.1 hi)
          exact tcx_termU (hA i) ho
      have hcd := tcx_capdiff X.p (X.seg C0 CE1 CE2 j) b b' l _ (by positivity) hterm
      have hcdR := (Int.cast_le (R := ℝ)).2 hcd
      push_cast at hcdR
      have hsN : ((segS X.TT j : ℕ) : ℝ) ≤ X.N1 := by exact_mod_cast (St.segB j).2
      have hD0 : (0 : ℝ) ≤ 3 * ((X.m : ℝ) + 1) + 2 * ((X.p : ℝ) ^ X.G' * e) := by positivity
      have hsD := mul_le_mul_of_nonneg_right hsN hD0
      have hVR := (Int.cast_le (R := ℝ)).2 hV
      push_cast at hVR
      rw [add_assoc]
      apply tcx_floor
      rw [hne]
      push_cast
      rw [hkdef, hQdef] at hnumB
      have e1 : (mm + (n : ℝ) * ka1 X) - (mm + ((n : ℝ) - e) * ka1 X) = e * ka1 X := by ring
      have e2 : (X.N1 : ℝ) * (3 * ((X.m : ℝ) + 1) + 2 * ((X.p : ℝ) ^ X.G' * e)) =
          (X.N1 : ℝ) * (3 * ((X.m : ℝ) + 1) + 2 * ((X.p : ℝ) ^ X.G' * e)) := rfl
      linarith

theorem restNumCore : RestNumCore :=
  TransportedAlt.mono (fun _ _ _ _ _ _ _ _ _ _ h => numCore_of_std h.2) thr_std

end Formalism.MainNotions.ColumnSystems.Pf
