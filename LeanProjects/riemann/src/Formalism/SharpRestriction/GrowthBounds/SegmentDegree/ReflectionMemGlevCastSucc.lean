import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.ColumnConditionsOfNumericBounds

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

def OldestLetterInSegment : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r), X.Hyp p K → ∀ j, ∀ x ∈ X.toLate j,
    X.F.oldest j x ∈ X.F.letters j ∧ (¬ X.F.IsW j (X.F.oldest j x) → X.F.oldest j x ∈ X.F.LLset j)

def OrderNumericBound (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r), X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ j, ∀ x ∈ X.toLate j,
      ((p ^ X.Rj p K j : ℕ) : ℝ) * X.oc p K j x + Dat.k (r := r) K * ((p ^ X.Rj p K j : ℕ) : ℝ) ≤ X.o p K j x

section Num

variable {p n' r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] {X : Dat n' r}

theorem frame_zero_le {F : Frames n' r} {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁) (j : ℤ) : ∀ i, i < r → F.fr j 0 ≤ F.fr j i := by
  intro i
  induction i with
  | zero => intro _; exact le_rfl
  | succ i ih => intro h; exact (ih (by omega)).trans (hV.2.2.1 j i h).le

theorem reflection_mem_Glev_castSucc {F : Frames n' r} {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁) (j : ℤ) : F.fr (j - 1) 0 ∈ F.letters j := by
  have hr : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have h1 := frame_zero_le hV (j - 1) (r - 1) (by omega)
  have h2 := hV.2.2.2.1 (j - 1)
  rw [sub_add_cancel] at h2
  have h3 := frame_zero_le hV j (r - 1) (by omega)
  simp only [Frames.letters, Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨le_rfl, by omega⟩, (hV.2.2.2.2.1 (j - 1) 0 hr).1⟩

theorem mem_letters_bounds {F : Frames n' r} {j x : ℤ} (hx : x ∈ F.letters j) :
    F.fr (j - 1) 0 ≤ x ∧ x ≤ F.fr j (r - 1) ∧ posOf n' x ∈ F.TT := by
  simp only [Frames.letters, Finset.mem_filter, Finset.mem_Icc] at hx
  exact ⟨hx.1.1, hx.1.2, hx.2⟩

structure Basics (X : Dat n' r) (p K : ℕ) : Prop where
  p1 : (1 : ℝ) < p
  Ns1 : (1 : ℝ) ≤ X.Ns
  k5 : (5 : ℝ) ≤ Dat.k (r := r) K
  rk : (r : ℝ) ≤ Dat.k (r := r) K
  Q1 : (1 : ℝ) ≤ X.Q
  Y1 : (1 : ℝ) ≤ X.Y

theorem basics (hX : X.Hyp p K) : Basics X p K := by
  have hV := hX.valid
  have hw := reflection_mem_Glev_castSucc hV 0
  have hp : (13 : ℝ) ≤ p := by exact_mod_cast hX.p13
  have hc : 1 ≤ (X.F.letters 0).card := Finset.card_pos.mpr ⟨_, hw⟩
  have hNs : 1 ≤ X.Ns := hc.trans (hX.card 0)
  have hK := hX.NsK
  have hr := hX.r2
  have hQ := hX.twist 0 _ hw
  refine ⟨by linarith, by exact_mod_cast hNs, ?_, ?_, ?_, hX.Y1⟩
  · unfold Dat.k
    exact_mod_cast (by omega : 5 ≤ r + K)
  · unfold Dat.k
    exact_mod_cast (by omega : r ≤ r + K)
  · exact le_trans (one_le_pow₀ (by linarith : (1 : ℝ) ≤ p)) hQ

def Tj (X : Dat n' r) (p K : ℕ) (j : ℤ) : ℝ :=
  X.a / (8 * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) * (p : ℝ) ^ X.F.dist j (X.F.fr (j - 1) 0))

theorem den_pos (hX : X.Hyp p K) (j : ℤ) :
    0 < 8 * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) * (p : ℝ) ^ X.F.dist j (X.F.fr (j - 1) 0) := by
  have B := basics hX
  have h1 : (0 : ℝ) < p := by linarith [B.p1]
  have h2 : (0 : ℝ) < X.Y := by linarith [B.Y1]
  have h3 : (0 : ℝ) < Dat.k (r := r) K := by linarith [B.k5]
  have h4 : (0 : ℝ) < X.Ns := by linarith [B.Ns1]
  positivity

theorem Tj_ge (hX : X.Hyp p K) (j : ℤ) : 4 * (p : ℝ) * ((X.E₀ : ℝ) + X.mStar + 1) ≤ Tj X p K j := by
  have b := basics hX
  have hd := den_pos hX j
  have hw := reflection_mem_Glev_castSucc hX.valid j
  have hQ := hX.twist j _ hw
  have P3 := hX.P3
  have hY : 0 ≤ X.Y := by linarith [b.Y1]
  have hp0 : (0 : ℝ) ≤ p := by linarith [b.p1]
  have hdQ : (p : ℝ) ^ X.F.dist j (X.F.fr (j - 1) 0) ≤ X.Q ^ 2 := hQ.trans (by nlinarith [b.Q1])
  have hk : Dat.k (r := r) K = ((r + K : ℕ) : ℝ) := rfl
  have hc : 0 ≤ (p : ℝ) * X.Y * ((r + K : ℕ) : ℝ) ^ 2 * (X.Ns : ℝ) * ((X.E₀ : ℝ) + X.mStar + 1) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hp0 hY) (sq_nonneg _)) (Nat.cast_nonneg _))
      (by positivity)
  have hm := mul_le_mul_of_nonneg_left hdQ hc
  unfold Tj
  rw [le_div_iff₀ hd, hk]
  calc 4 * (p : ℝ) * ((X.E₀ : ℝ) + X.mStar + 1) * (8 * X.Y * ((r + K : ℕ) : ℝ) ^ 2 * (X.Ns : ℝ) * (p : ℝ) ^ X.F.dist j (X.F.fr (j - 1) 0))
        = 32 * ((p : ℝ) * X.Y * ((r + K : ℕ) : ℝ) ^ 2 * (X.Ns : ℝ) * ((X.E₀ : ℝ) + X.mStar + 1) * (p : ℝ) ^ X.F.dist j (X.F.fr (j - 1) 0)) := by ring
    _ ≤ 32 * ((p : ℝ) * X.Y * ((r + K : ℕ) : ℝ) ^ 2 * (X.Ns : ℝ) * ((X.E₀ : ℝ) + X.mStar + 1) * X.Q ^ 2) := by linarith
    _ = 32 * (p : ℝ) * X.Y * ((r + K : ℕ) : ℝ) ^ 2 * (X.Ns : ℝ) * X.Q ^ 2 * ((X.E₀ : ℝ) + X.mStar + 1) := by ring
    _ ≤ X.a := P3

theorem pow_Rj_le (hX : X.Hyp p K) (j : ℤ) : ((p : ℝ) ^ X.Rj p K j) ≤ Tj X p K j := by
  have B := basics hX
  have hT := Tj_ge hX j
  have hT1 : (1 : ℝ) ≤ Tj X p K j := by
    have h0 : (0 : ℝ) ≤ (X.E₀ : ℝ) + X.mStar := by positivity
    nlinarith [B.p1]
  have hfl : ⌊Tj X p K j⌋₊ ≠ 0 := by
    have : 1 ≤ ⌊Tj X p K j⌋₊ := Nat.le_floor (by simpa using hT1)
    omega
  have h1 : p ^ X.Rj p K j ≤ ⌊Tj X p K j⌋₊ := Nat.pow_log_le_self p hfl
  have h2 : ((⌊Tj X p K j⌋₊ : ℕ) : ℝ) ≤ Tj X p K j := Nat.floor_le (by linarith)
  have h3 : ((p ^ X.Rj p K j : ℕ) : ℝ) ≤ ((⌊Tj X p K j⌋₊ : ℕ) : ℝ) := by exact_mod_cast h1
  push_cast at h3
  linarith

theorem lt_pow_Rj (hX : X.Hyp p K) (j : ℤ) : Tj X p K j < (p : ℝ) ^ (X.Rj p K j + 1) := by
  have h1 : ⌊Tj X p K j⌋₊ < p ^ (X.Rj p K j + 1) := Nat.lt_pow_succ_log_self hX.prime.one_lt _
  have h2 : Tj X p K j < (⌊Tj X p K j⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have h3 : ((⌊Tj X p K j⌋₊ : ℕ) : ℝ) + 1 ≤ ((p ^ (X.Rj p K j + 1) : ℕ) : ℝ) := by exact_mod_cast h1
  push_cast at h3
  linarith

theorem power_exceeds_max_multiplicity (C₀ : ℝ) : PowerExceedsMaxMultiplicity C₀ := by
  intro p n' r K _ _ _ X hX _ _ j
  have B := basics hX
  have h1 := Tj_ge hX j
  have h2 := lt_pow_Rj hX j
  rw [pow_succ] at h2
  have hp : (0 : ℝ) < p := by linarith [B.p1]
  have hE : (0 : ℝ) ≤ X.E₀ := Nat.cast_nonneg _
  have hm : (0 : ℝ) ≤ X.mStar := Nat.cast_nonneg _
  have h3 : 4 * ((X.E₀ : ℝ) + X.mStar + 1) < (p : ℝ) ^ X.Rj p K j := by
    by_contra hcon
    push_neg at hcon
    have := mul_le_mul_of_nonneg_right hcon hp.le
    nlinarith
  have h4 : (X.mStar : ℝ) < ((p ^ X.Rj p K j : ℕ) : ℝ) := by push_cast; linarith
  exact_mod_cast h4

theorem l42b (hX : X.Hyp p K) (j y : ℤ) (hy : y ∈ X.F.letters j) :
    8 * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) * (p : ℝ) ^ (X.F.dist j y + X.Rj p K j) ≤ X.a := by
  have b := basics hX
  have hd := den_pos hX j
  have hy' := mem_letters_bounds hy
  have hdist : X.F.dist j y ≤ X.F.dist j (X.F.fr (j - 1) 0) := by
    unfold Frames.dist
    exact Int.toNat_le_toNat (by linarith [hy'.1])
  have hp1 : (1 : ℝ) ≤ p := b.p1.le
  have hpow : (p : ℝ) ^ X.F.dist j y ≤ (p : ℝ) ^ X.F.dist j (X.F.fr (j - 1) 0) := pow_le_pow_right₀ hp1 hdist
  have hR := pow_Rj_le hX j
  have hY : 0 ≤ X.Y := by linarith [b.Y1]
  have hTa : 8 * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) * (p : ℝ) ^ X.F.dist j (X.F.fr (j - 1) 0) * Tj X p K j = X.a := by
    unfold Tj
    exact mul_div_cancel₀ _ hd.ne'
  have hc0 : 0 ≤ 8 * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hY) (sq_nonneg _)) (Nat.cast_nonneg _)
  have hm := mul_le_mul_of_nonneg_left (mul_le_mul hpow hR (pow_nonneg (by linarith) _) (pow_nonneg (by linarith) _)) hc0
  rw [pow_add]
  calc 8 * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) * ((p : ℝ) ^ X.F.dist j y * (p : ℝ) ^ X.Rj p K j)
      ≤ 8 * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) * ((p : ℝ) ^ X.F.dist j (X.F.fr (j - 1) 0) * Tj X p K j) := hm
    _ = X.a := by rw [← hTa]; ring

end Num

end Formalism.MainNotions.SelectionLemmas.Pf
