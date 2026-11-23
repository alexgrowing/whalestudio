import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.SumPosOfPer

noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Finset Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

section Num

variable {p n' r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] {X : Dat n' r}

theorem Rj_add_first_frame_gap_le_last_frame_gap_add_Rj_succ (hX : X.Hyp p K) (j : ℤ) :
    (X.Rj p K j : ℤ) + (X.F.fr j 0 - X.F.fr (j - 1) 0) ≤
      X.F.fr (j + 1) (r - 1) - X.F.fr j (r - 1) + X.Rj p K (j + 1) := by
  have B := basics hX
  have h1 := pow_Rj_le hX j
  have h2 := lt_pow_Rj hX (j + 1)
  have d1 := den_pos hX j
  have d2 := den_pos hX (j + 1)
  unfold Tj at h1 h2
  rw [le_div_iff₀ d1] at h1
  rw [div_lt_iff₀ d2] at h2
  simp only [add_sub_cancel_right] at h2
  have hc0 : 0 < 8 * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) := by
    have h2 : (0 : ℝ) < X.Y := by linarith [B.Y1]
    have h3 : (0 : ℝ) < Dat.k (r := r) K := by linarith [B.k5]
    have h4 : (0 : ℝ) < X.Ns := by linarith [B.Ns1]
    positivity
  have h3 : (p : ℝ) ^ (X.Rj p K j + X.F.dist j (X.F.fr (j - 1) 0)) <
      (p : ℝ) ^ (X.Rj p K (j + 1) + 1 + X.F.dist (j + 1) (X.F.fr j 0)) := by
    rw [pow_add, pow_add _ (X.Rj p K (j + 1) + 1)]
    refine lt_of_mul_lt_mul_right ?_ hc0.le
    calc (p : ℝ) ^ X.Rj p K j * (p : ℝ) ^ X.F.dist j (X.F.fr (j - 1) 0) * (8 * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ))
        = (p : ℝ) ^ X.Rj p K j * (8 * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) * (p : ℝ) ^ X.F.dist j (X.F.fr (j - 1) 0)) := by
          ring
      _ ≤ X.a := h1
      _ < _ := h2
      _ = _ := by ring
  have h4 := (pow_lt_pow_iff_right₀ B.p1).mp h3
  have b1 := mem_letters_bounds (reflection_mem_Glev_castSucc hX.valid j)
  have b2 := mem_letters_bounds (reflection_mem_Glev_castSucc hX.valid (j + 1))
  simp only [add_sub_cancel_right] at b2
  unfold Frames.dist at h4
  omega

theorem frame_zero_strict_mono (hX : X.Hyp p K) (j : ℤ) : X.F.fr (j - 1) 0 < X.F.fr j 0 := by
  have h1 := hX.valid.2.2.2.1 (j - 1)
  rw [sub_add_cancel] at h1
  exact lt_of_le_of_lt (fr_zero_le_eFr hX.valid (j - 1)) h1

theorem sum_PzQc (hX : X.Hyp p K) (j v : ℤ) (hv : v ≤ X.F.fr j (r - 1)) :
    X.Pz p K j v * X.Qc p K j = p ^ (X.F.dist (j + 1) v + X.Rj p K (j + 1)) := by
  have h := Rj_add_first_frame_gap_le_last_frame_gap_add_Rj_succ hX j
  have h0 := frame_zero_strict_mono hX j
  have hm : X.F.fr j (r - 1) < X.F.fr (j + 1) (r - 1) := eFr_strictMono hX.valid (by omega : j < j + 1)
  unfold Dat.Pz Dat.Qc
  rw [← pow_add]
  congr 1
  unfold Frames.dist
  omega

theorem sum_prodQ (hX : X.Hyp p K) : ∏ j ∈ Finset.range X.F.J, X.Qc p K (j : ℤ) = p ^ n' := by
  unfold Dat.Qc
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  have key : ((∑ j ∈ Finset.range X.F.J, (X.F.fr ((j : ℤ) + 1) (r - 1) - X.F.fr (j : ℤ) (r - 1) +
      (X.Rj p K ((j : ℤ) + 1) : ℤ) - (X.Rj p K (j : ℤ) : ℤ)).toNat : ℕ) : ℤ) = n' := by
    push_cast
    have e : ∀ j ∈ Finset.range X.F.J, (((X.F.fr ((j : ℤ) + 1) (r - 1) - X.F.fr (j : ℤ) (r - 1) +
        (X.Rj p K ((j : ℤ) + 1) : ℤ) - (X.Rj p K (j : ℤ) : ℤ)).toNat : ℕ) : ℤ) =
        (fun i : ℕ => X.F.fr (i : ℤ) (r - 1) + (X.Rj p K (i : ℤ) : ℤ)) (j + 1) -
          (fun i : ℕ => X.F.fr (i : ℤ) (r - 1) + (X.Rj p K (i : ℤ) : ℤ)) j := by
      intro j _
      have h := Rj_add_first_frame_gap_le_last_frame_gap_add_Rj_succ hX (j : ℤ)
      have h0 := frame_zero_strict_mono hX (j : ℤ)
      rw [Int.toNat_of_nonneg (by omega)]
      push_cast
      ring
    have tel := Finset.sum_range_sub (fun i : ℕ => X.F.fr (i : ℤ) (r - 1) + (X.Rj p K (i : ℤ) : ℤ)) X.F.J
    rw [Finset.sum_congr rfl e]
    refine tel.trans ?_
    have p1 := fr_add_mul_period hX.valid 0 (r - 1) 1
    have p2 := sum_Rj_per X p K hX.valid 0 1
    simp only [zero_add, one_mul] at p1 p2
    beta_reduce
    rw [p1, p2]
    push_cast
    ring
  exact_mod_cast key

theorem thirty_two_Y_le_a (hX : X.Hyp p K) : 32 * X.Y ≤ X.a := by
  have B := basics hX
  refine le_trans ?_ (l42b hX 0 _ (reflection_mem_Glev_castSucc hX.valid 0))
  have h1 : (1 : ℝ) ≤ (p : ℝ) ^ (X.F.dist 0 (X.F.fr (0 - 1) 0) + X.Rj p K 0) := one_le_pow₀ B.p1.le
  have hk2 : (25 : ℝ) ≤ Dat.k (r := r) K ^ 2 := by nlinarith [B.k5]
  have hY0 : (0 : ℝ) < X.Y := by linarith [B.Y1]
  have h2 : 32 * X.Y ≤ 8 * X.Y * Dat.k (r := r) K ^ 2 := by nlinarith
  have h3 : 8 * X.Y * Dat.k (r := r) K ^ 2 ≤ 8 * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) :=
    le_mul_of_one_le_right (by positivity) B.Ns1
  have h4 : 8 * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) ≤
      8 * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) * (p : ℝ) ^ (X.F.dist 0 (X.F.fr (0 - 1) 0) + X.Rj p K 0) :=
    le_mul_of_one_le_right (by have := B.Ns1; positivity) h1
  linarith

theorem sum_aP (hX : X.Hyp p K) (hLa : (1088 : ℝ) ≤ X.CLa) (hk : (1088 : ℝ) ≤ X.Ck) (j y : ℤ)
    (hy : y ∈ X.F.letters j) :
    (36 / 5 : ℝ) * (X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) * (p : ℝ) ^ (X.F.dist j y + X.Rj p K j)) ≤
      (X.a' p K (posOf n' y) : ℝ) := by
  have h41 := (top_count_lower_bounds_of_occurrence 1088 (by norm_num) top_occurs_in_at_most_two_segments p n' r K X hX hLa hk).1 _ (mem_letters_bounds hy).2.2
  have hd := (hX.degs _ (mem_letters_bounds hy).2.2).1
  have h2 := l42b hX j y hy
  linarith

theorem sum_kP (hX : X.Hyp p K) (hLa : (1088 : ℝ) ≤ X.CLa) (hk : (1088 : ℝ) ≤ X.Ck) (j x : ℤ)
    (hx : x ∈ X.toLate j) : (r + K) * X.Pz p K j x ≤ X.a' p K (posOf n' x) := by
  have B := basics hX
  have h := sum_aP hX hLa hk j x (sum_late_mem hx).1
  have hP : (0 : ℝ) < (p : ℝ) ^ (X.F.dist j x + X.Rj p K j) := by
    have : (0 : ℝ) < p := by linarith [B.p1]
    positivity
  have h1 : Dat.k (r := r) K ≤ X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) := by
    have hk0 : (0 : ℝ) < Dat.k (r := r) K := by linarith [B.k5]
    have a1 : Dat.k (r := r) K ≤ Dat.k (r := r) K ^ 2 := by nlinarith [B.k5]
    have a2 : Dat.k (r := r) K ^ 2 ≤ X.Y * Dat.k (r := r) K ^ 2 := le_mul_of_one_le_left (by positivity) B.Y1
    have a3 : X.Y * Dat.k (r := r) K ^ 2 ≤ X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) :=
      le_mul_of_one_le_right (by have := B.Y1; positivity) B.Ns1
    linarith
  have h2 := mul_le_mul_of_nonneg_right h1 hP.le
  have h3 : Dat.k (r := r) K * (p : ℝ) ^ (X.F.dist j x + X.Rj p K j) ≤ (X.a' p K (posOf n' x) : ℝ) := by
    have : 0 ≤ X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) * (p : ℝ) ^ (X.F.dist j x + X.Rj p K j) := by
      have := B.Y1; have := B.Ns1; positivity
    linarith
  unfold Dat.k at h3
  unfold Dat.Pz
  exact_mod_cast h3

theorem sumBin_eq (n : ℕ) : sumBin r K n = (((n + (r + K - 1)).choose (r + K - 1) : ℕ) : ℝ) := by
  unfold sumBin
  have : n + (r + K) - 1 = n + (r + K - 1) := Nat.add_sub_assoc (by have := NeZero.pos r; omega) n
  rw [this]

theorem sum_M_le : ((r + K - 1 : ℕ) : ℝ) ≤ Dat.k (r := r) K := by
  unfold Dat.k
  exact_mod_cast Nat.sub_le _ _

theorem sum_compA (hX : X.Hyp p K) (hLa : (1088 : ℝ) ≤ X.CLa) (hk : (1088 : ℝ) ≤ X.Ck) (t : Fin n')
    (ht : t ∈ X.F.TT) : sumBin r K (X.deg t) * (1 - 5 / X.Y) ≤ sumBin r K (X.a' p K t) := by
  have B := basics hX
  have hk0 : (0 : ℝ) < Dat.k (r := r) K := by linarith [B.k5]
  have hY0 : (0 : ℝ) < X.Y := by linarith [B.Y1]
  have hu : 0 < Dat.k (r := r) K * X.Y := by positivity
  have ha0 : 0 ≤ X.a := by have := thirty_two_Y_le_a hX; linarith

  have hE0 : (X.E₀ : ℝ) * (Dat.k (r := r) K * X.Y) ≤ X.a := by
    have h1 := Tj_ge hX 0
    have d1 := den_pos hX 0
    unfold Tj at h1
    rw [le_div_iff₀ d1] at h1
    have hp1 : (1 : ℝ) ≤ (p : ℝ) ^ X.F.dist 0 (X.F.fr (0 - 1) 0) := one_le_pow₀ B.p1.le
    have w1 : Dat.k (r := r) K * X.Y ≤
        8 * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) * (p : ℝ) ^ X.F.dist 0 (X.F.fr (0 - 1) 0) := by
      have a1 : Dat.k (r := r) K * X.Y ≤ 8 * X.Y * Dat.k (r := r) K ^ 2 := by nlinarith [B.k5]
      have a2 : 8 * X.Y * Dat.k (r := r) K ^ 2 ≤ 8 * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) :=
        le_mul_of_one_le_right (by positivity) B.Ns1
      have a3 : 8 * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) ≤
          8 * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) * (p : ℝ) ^ X.F.dist 0 (X.F.fr (0 - 1) 0) :=
        le_mul_of_one_le_right (by have := B.Ns1; positivity) hp1
      linarith
    have hE : (X.E₀ : ℝ) ≤ 4 * (p : ℝ) * ((X.E₀ : ℝ) + X.mStar + 1) := by
      have e0 : (0 : ℝ) ≤ X.E₀ := Nat.cast_nonneg _
      have m0 : (0 : ℝ) ≤ X.mStar := Nat.cast_nonneg _
      nlinarith [B.p1]
    calc (X.E₀ : ℝ) * (Dat.k (r := r) K * X.Y)
        ≤ (4 * (p : ℝ) * ((X.E₀ : ℝ) + X.mStar + 1)) *
          (8 * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) * (p : ℝ) ^ X.F.dist 0 (X.F.fr (0 - 1) 0)) :=
          mul_le_mul hE w1 hu.le (le_trans (Nat.cast_nonneg _) hE)
      _ ≤ X.a := h1

  have hEt : (X.Et p K t : ℝ) * (Dat.k (r := r) K * X.Y) ≤ 4 * X.a := by
    have h1 := Et_le top_occurs_in_at_most_two_segments hX t
    rw [le_div_iff₀ (by positivity)] at h1
    have hNk : (X.Ns : ℝ) ≤ Dat.k (r := r) K := by
      unfold Dat.k
      have := hX.NsK
      exact_mod_cast (by omega : X.Ns ≤ r + K)
    have h2 : 4 * (X.Ns : ℝ) * X.a ≤ 4 * Dat.k (r := r) K * X.a := by nlinarith
    have h3 : Dat.k (r := r) K * ((X.Et p K t : ℝ) * (Dat.k (r := r) K * X.Y)) ≤ Dat.k (r := r) K * (4 * X.a) := by
      nlinarith
    exact le_of_mul_le_mul_left h3 hk0
  have hdeg := (hX.degs t ht).1
  have hnat : X.deg t ≤ X.a' p K t + X.E' t + X.Et p K t := by
    unfold Dat.a' Dat.d
    rw [if_pos ht]
    omega
  have hnat' : (X.deg t : ℝ) ≤ (X.a' p K t : ℝ) + X.E' t + X.Et p K t := by exact_mod_cast hnat
  have hE' : (X.E' t : ℝ) ≤ X.E₀ := by exact_mod_cast hX.E'le t ht
  set θ : ℝ := 5 / (Dat.k (r := r) K * X.Y) with hθ
  have hθ0 : 0 ≤ θ := by positivity
  have hθ1 : θ ≤ 1 := by
    rw [hθ, div_le_one hu]
    nlinarith [B.k5, B.Y1]
  have key : (X.E₀ : ℝ) + X.Et p K t ≤ θ * X.deg t := by
    rw [hθ, div_mul_eq_mul_div, le_div_iff₀ hu]
    nlinarith
  have hcmp := choose_add_mul_one_sub_le_pow_mul_choose_add (X.a' p K t) (X.deg t) (r + K - 1) 1 θ hθ1 (fun l _ => by
    have hl : (0 : ℝ) ≤ θ * (1 + l) := by positivity
    calc ((X.deg t : ℝ) + 1 + l) * (1 - θ) = (X.deg t : ℝ) + 1 + l - θ * X.deg t - θ * (1 + l) := by ring
      _ ≤ 1 * ((X.a' p K t : ℝ) + 1 + l) := by linarith)
  rw [one_pow, one_mul] at hcmp
  rw [sumBin_eq, sumBin_eq]
  refine le_trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)) hcmp
  have hM := sum_M_le (r := r) (K := K)
  have : ((r + K - 1 : ℕ) : ℝ) * θ ≤ 5 / X.Y := by
    calc ((r + K - 1 : ℕ) : ℝ) * θ ≤ Dat.k (r := r) K * θ := mul_le_mul_of_nonneg_right hM hθ0
      _ = 5 / X.Y := by rw [hθ]; field_simp
  linarith

theorem sum_compW (hX : X.Hyp p K) (hLa : (1088 : ℝ) ≤ X.CLa) (hk : (1088 : ℝ) ≤ X.Ck) (j : ℤ) (i : Fin r) :
    sumBin r K (X.a' p K (posOf n' (X.F.fr j i.val))) * (1 - 1 / X.Y) ≤
    (((X.Pz p K j (X.F.fr j i.val) * X.Qc p K j : ℕ) : ℝ)) ^ (r + K - 1) *
      sumBin r K ((X.Bw p K (j + 1) (X.F.fr j i.val) - (X.m0 K : ℤ)).toNat) := by
  classical
  have B := basics hX
  have hk0 : (0 : ℝ) < Dat.k (r := r) K := by linarith [B.k5]
  have hY0 : (0 : ℝ) < X.Y := by linarith [B.Y1]
  have hu : 0 < Dat.k (r := r) K * X.Y := by positivity
  have hrr : r - 1 < r := Nat.sub_lt (NeZero.pos r) Nat.one_pos
  have hvle : X.F.fr j i.val ≤ X.F.fr j (r - 1) := sum_fr_le hX.valid j i.val (r - 1) (by have := i.isLt; omega) hrr
  have hvlet : X.F.fr j i.val ∈ X.F.letters (j + 1) := by
    unfold Frames.letters
    rw [Finset.mem_filter, Finset.mem_Icc, add_sub_cancel_right]
    refine ⟨⟨fr_zero_le hX.valid j i.val i.isLt, ?_⟩, (hX.valid.2.2.2.2.1 j i.val i.isLt).1⟩
    exact hvle.trans (eFr_strictMono hX.valid (by omega : j < j + 1)).le
  rw [sum_PzQc hX j _ hvle]
  have hn := sum_aP hX hLa hk (j + 1) _ hvlet
  set v := X.F.fr j i.val
  set P' : ℕ := p ^ (X.F.dist (j + 1) v + X.Rj p K (j + 1)) with hP'
  set n : ℕ := X.a' p K (posOf n' v) with hnn
  have hP'0 : 0 < P' := pow_pos hX.prime.pos _
  have hP'r : (0 : ℝ) < (P' : ℝ) := by exact_mod_cast hP'0
  have hP'1 : (1 : ℝ) ≤ (P' : ℝ) := by exact_mod_cast hP'0
  have hn' : (36 / 5 : ℝ) * (X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) * (P' : ℝ)) ≤ (n : ℝ) := by
    rw [hP']; push_cast; exact hn
  set Bn : ℕ := (X.Bw p K (j + 1) v - (X.m0 K : ℤ)).toNat with hBn
  have hB1 : ((X.Bw p K (j + 1) v - (X.m0 K : ℤ) : ℤ) : ℝ) ≤ (Bn : ℝ) := by
    exact_mod_cast Int.self_le_toNat _
  have hB2 : ((X.Bw p K (j + 1) v - (X.m0 K : ℤ) : ℤ) : ℝ) =
      ((n / P' : ℕ) : ℝ) - (Dat.k (r := r) K + r + 1) - (Dat.k (r := r) K * X.Ns + 1) := by
    have hBw : X.Bw p K (j + 1) v = ((n / P' : ℕ) : ℤ) - ((r + K + r + 1 : ℕ) : ℤ) := rfl
    rw [hBw]
    unfold Dat.m0 Dat.k
    generalize n / P' = q
    push_cast
    ring
  have hdiv := natDiv_gt n P' hP'0
  have hrk := B.rk
  have hc : Dat.k (r := r) K + r + 3 + Dat.k (r := r) K * X.Ns ≤ 4 * (Dat.k (r := r) K * X.Ns) := by
    have : Dat.k (r := r) K ≤ Dat.k (r := r) K * X.Ns := le_mul_of_one_le_right hk0.le B.Ns1
    linarith [B.k5]
  have hPB : (n : ℝ) - 4 * (Dat.k (r := r) K * X.Ns) * P' ≤ (P' : ℝ) * Bn := by
    have h1 : (n : ℝ) / P' - 1 - (Dat.k (r := r) K + r + 1) - (Dat.k (r := r) K * X.Ns + 1) ≤ (Bn : ℝ) := by
      linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hP'r.le
    have h3 : (P' : ℝ) * ((n : ℝ) / P') = n := by field_simp
    have h4 := mul_le_mul_of_nonneg_right hc hP'r.le
    nlinarith
  set θ : ℝ := 1 / (Dat.k (r := r) K * X.Y) with hθ
  have hθ0 : 0 ≤ θ := by positivity
  have hθ1 : θ ≤ 1 := by
    rw [hθ, div_le_one hu]
    nlinarith [B.k5, B.Y1]
  have key : 4 * (Dat.k (r := r) K * X.Ns) * P' ≤ θ * n := by
    rw [hθ, div_mul_eq_mul_div, one_mul, le_div_iff₀ hu]
    have : 4 * (Dat.k (r := r) K * X.Ns) * P' * (Dat.k (r := r) K * X.Y) =
        4 * (X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) * (P' : ℝ)) := by ring
    rw [this]
    have h0 : 0 ≤ X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) * (P' : ℝ) := by
      have := B.Ns1; positivity
    linarith
  have hcmp := choose_add_mul_one_sub_le_pow_mul_choose_add Bn n (r + K - 1) (P' : ℝ) θ hθ1 (fun l _ => by
    have hl : (0 : ℝ) ≤ θ * (1 + l) := by positivity
    have hl2 : (1 : ℝ) + l ≤ (P' : ℝ) * (1 + l) := le_mul_of_one_le_left (by positivity) hP'1
    calc ((n : ℝ) + 1 + l) * (1 - θ) = (n : ℝ) + 1 + l - θ * n - θ * (1 + l) := by ring
      _ ≤ (P' : ℝ) * Bn + (P' : ℝ) * (1 + l) := by linarith
      _ = (P' : ℝ) * ((Bn : ℝ) + 1 + l) := by ring)
  rw [sumBin_eq, sumBin_eq]
  refine le_trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)) hcmp
  have hM := sum_M_le (r := r) (K := K)
  have : ((r + K - 1 : ℕ) : ℝ) * θ ≤ 1 / X.Y := by
    calc ((r + K - 1 : ℕ) : ℝ) * θ ≤ Dat.k (r := r) K * θ := mul_le_mul_of_nonneg_right hM hθ0
      _ = 1 / X.Y := by rw [hθ]; field_simp
  linarith

theorem sum_facts (hX : X.Hyp p K) (hLa : (1088 : ℝ) ≤ X.CLa) (hk : (1088 : ℝ) ≤ X.Ck) : SumFacts X p K where
  tiling := prod_tiling X hX.valid
  split := sum_split X hX.valid
  LLsub := sum_LLsub X hX.valid
  frlate := sum_frlate X hX.valid
  uniqP := sum_uniqP X p K hX.valid
  kP := sum_kP hX hLa hk
  compA := sum_compA hX hLa hk
  compW := sum_compW hX hLa hk
  prodQ := sum_prodQ hX
  perW := sum_perW X p K hX.valid
  JN := J_le_card_TT_of_valid X hX.valid
  a32 := thirty_two_Y_le_a hX

end Num

theorem restSum : RestSum 1088 1 :=
  restSum_of fun p n' r K _ _ _ X hX hLa hk => ⟨sum_facts hX hLa hk, Ns_one_le hX⟩

end Formalism.MainNotions.SelectionLemmas.Pf
