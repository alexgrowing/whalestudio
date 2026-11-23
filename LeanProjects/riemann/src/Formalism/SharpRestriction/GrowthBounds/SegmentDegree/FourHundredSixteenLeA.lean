import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.SortGetDSpec
import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.ThresholdPowerBoundOfCounts

noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf.TE

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace Formalism.MainNotions.SelectionLemmas.Pf.T

section Num61

variable {p n' r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] {X : Dat n' r}

private theorem fr_lt_fr_of_lt {F : Frames n' r} {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁) (j : ℤ) :
    ∀ i i', i < i' → i' < r → F.fr j i < F.fr j i' := by
  intro i i' hii' hi'
  induction i' with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hii' with h | h
    · exact (ih h (by omega)).trans (hV.2.2.1 j k hi')
    · subst h
      exact hV.2.2.1 j i hi'

private theorem fr_le_fr_of_le {F : Frames n' r} {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁) (j : ℤ) (i : ℕ)
    (hi : i < r) : F.fr j 0 ≤ F.fr j i := by
  rcases Nat.eq_zero_or_pos i with h | h
  · rw [h]
  · exact (fr_lt_fr_of_lt hV j 0 i h hi).le

private theorem fr_le_fr_last {F : Frames n' r} {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁) (j : ℤ) (i : ℕ)
    (hi : i < r) : F.fr j i ≤ F.fr j (r - 1) := by
  rcases Nat.lt_or_ge i (r - 1) with h | h
  · exact (fr_lt_fr_of_lt hV j i (r - 1) h (by omega)).le
  · rw [show i = r - 1 by omega]

private theorem fr_one_zero_mem_letters_one {F : Frames n' r} {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁) (hr : 1 ≤ r) :
    F.fr 1 0 ∈ F.letters 1 := by
  have hg : F.fr 0 (r - 1) < F.fr 1 0 := by
    have h0 := hV.2.2.2.1 0
    simpa using h0
  simp only [Frames.letters, sub_self, Finset.mem_filter, Finset.mem_Icc]
  refine ⟨⟨?_, fr_le_fr_of_le hV 1 (r - 1) (by omega)⟩, (hV.2.2.2.2.1 1 0 (by omega)).1⟩
  have h1 := fr_le_fr_of_le hV 0 (r - 1) (by omega)
  omega

theorem six_le_Ns (hX : X.Hyp p K) : 6 ≤ X.Ns := by
  have hV := hX.valid
  have hr2 := hX.r2
  have hg : X.F.fr 0 (r - 1) < X.F.fr 1 0 := by
    have h0 := hV.2.2.2.1 0
    simpa using h0
  have hle : ∀ j : ℤ, ∀ i, i < r → X.F.fr j 0 ≤ X.F.fr j i := fun j i hi => fr_le_fr_of_le hV j i hi
  have hleT : ∀ j : ℤ, ∀ i, i < r → X.F.fr j i ≤ X.F.fr j (r - 1) := fun j i hi => fr_le_fr_last hV j i hi
  have hinj : ∀ j : ℤ, Set.InjOn (fun i => X.F.fr j i) (Finset.range r) := by
    intro j a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    simp only at hab
    rcases lt_trichotomy a b with h | h | h
    · have h2 := fr_lt_fr_of_lt hV j a b h hb
      omega
    · exact h
    · have h2 := fr_lt_fr_of_lt hV j b a h ha
      omega
  have hAc : ((Finset.range r).image (fun i => X.F.fr 0 i)).card = r := by
    rw [Finset.card_image_of_injOn (hinj 0), Finset.card_range]
  have hCc : ((Finset.range r).image (fun i => X.F.fr 1 i)).card = r := by
    rw [Finset.card_image_of_injOn (hinj 1), Finset.card_range]
  have hBc : r ≤ (X.F.LLset 1).card := (hV.2.2.2.2.2.2.1 1).1
  have hsub : (Finset.range r).image (fun i => X.F.fr 0 i) ∪ X.F.LLset 1 ∪
      (Finset.range r).image (fun i => X.F.fr 1 i) ⊆ X.F.letters 1 := by
    intro x hx
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range] at hx
    simp only [Frames.letters, sub_self, Finset.mem_filter, Finset.mem_Icc]
    rcases hx with (⟨i, hi, rfl⟩ | hB) | ⟨i, hi, rfl⟩
    · refine ⟨⟨hle 0 i hi, ?_⟩, (hV.2.2.2.2.1 0 i hi).1⟩
      have h1 := hleT 0 i hi
      have h2 := hle 1 (r - 1) (by omega)
      omega
    · simp only [Frames.LLset, sub_self, Finset.mem_filter, Finset.mem_Ioo] at hB
      refine ⟨⟨?_, ?_⟩, hB.2⟩
      · have h1 := hle 0 (r - 1) (by omega)
        omega
      · have h1 := hle 1 (r - 1) (by omega)
        omega
    · refine ⟨⟨?_, hleT 1 i hi⟩, (hV.2.2.2.2.1 1 i hi).1⟩
      have h1 := hle 0 (r - 1) (by omega)
      have h2 := hle 1 i hi
      omega
  have hdAB : Disjoint ((Finset.range r).image (fun i => X.F.fr 0 i)) (X.F.LLset 1) := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    simp only [Finset.mem_image, Finset.mem_range] at hxA
    obtain ⟨i, hi, rfl⟩ := hxA
    simp only [Frames.LLset, sub_self, Finset.mem_filter, Finset.mem_Ioo] at hxB
    have h1 := hleT 0 i hi
    omega
  have hdABC : Disjoint ((Finset.range r).image (fun i => X.F.fr 0 i) ∪ X.F.LLset 1)
      ((Finset.range r).image (fun i => X.F.fr 1 i)) := by
    rw [Finset.disjoint_left]
    intro x hx hxC
    simp only [Finset.mem_image, Finset.mem_range] at hxC
    obtain ⟨i, hi, rfl⟩ := hxC
    have h1 := hle 1 i hi
    rcases Finset.mem_union.mp hx with hxA | hxB
    · simp only [Finset.mem_image, Finset.mem_range] at hxA
      obtain ⟨i', hi', he⟩ := hxA
      have h2 := hleT 0 i' hi'
      omega
    · simp only [Frames.LLset, sub_self, Finset.mem_filter, Finset.mem_Ioo] at hxB
      omega
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdABC, Finset.card_union_of_disjoint hdAB, hAc, hCc] at hcard
  have h3 := hX.card 1
  omega

theorem a_big (hX : X.Hyp p K) : 416 * (X.Ns : ℝ) ≤ X.a := by
  have hp : (13 : ℝ) ≤ p := by exact_mod_cast hX.p13
  have hY := hX.Y1
  have hk : (1 : ℝ) ≤ ((r + K : ℕ) : ℝ) := by
    have h0 := hX.r2
    exact_mod_cast (by omega : 1 ≤ r + K)
  have hmem := fr_one_zero_mem_letters_one hX.valid (by have := hX.r2; omega)
  have hQ : 1 ≤ X.Q := (one_le_pow₀ (by linarith : (1 : ℝ) ≤ p)).trans (hX.twist 1 _ hmem)
  have hE : (1 : ℝ) ≤ (X.E₀ : ℝ) + X.mStar + 1 := by
    have h1 : (0 : ℝ) ≤ X.E₀ := Nat.cast_nonneg _
    have h2 : (0 : ℝ) ≤ X.mStar := Nat.cast_nonneg _
    linarith
  calc 416 * (X.Ns : ℝ) = 32 * 13 * 1 * 1 ^ 2 * X.Ns * 1 ^ 2 * 1 := by ring
    _ ≤ 32 * p * X.Y * ((r + K : ℕ) : ℝ) ^ 2 * X.Ns * X.Q ^ 2 * ((X.E₀ : ℝ) + X.mStar + 1) := by
      gcongr
    _ ≤ X.a := hX.P3

theorem four_hundred_sixteen_le_a (hX : X.Hyp p K) : 416 ≤ X.a := by
  have h1 := a_big hX
  have h2 : (6 : ℝ) ≤ X.Ns := by exact_mod_cast six_le_Ns hX
  linarith

theorem log_a_ge (hX : X.Hyp p K) : 1 ≤ Real.log X.a := by
  have h := four_hundred_sixteen_le_a hX
  rw [Real.le_log_iff_exp_le (by linarith)]
  have h2 := Real.exp_one_lt_d9
  linarith

theorem k_big (hX : X.Hyp p K) (hk : 1088 ≤ X.Ck) : 1088 * (X.Ns : ℝ) ^ 2 ≤ ((r + K : ℕ) : ℝ) := by
  have hl := log_a_ge hX
  have hP1 := hX.P1
  have hN : (0 : ℝ) ≤ (X.Ns : ℝ) ^ 2 := by positivity
  have hC : (0 : ℝ) ≤ X.Ck := by linarith
  have h1 : 0 ≤ X.Ck * (X.Ns : ℝ) ^ 2 := mul_nonneg hC hN
  nlinarith [mul_le_mul_of_nonneg_left hl h1, mul_le_mul_of_nonneg_right hk hN]

theorem c_bounds (hX : X.Hyp p K) (h41 : ∀ t ∈ X.F.TT, (9 / 10 : ℝ) * (X.deg t : ℝ) ≤ (X.a' p K t : ℝ))
    (j y : ℤ) (hy : y ∈ X.F.letters j) :
    (36 / 5 : ℝ) * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) * (p : ℝ) ^ (X.F.dist j y + X.Rj p K j) ≤
        (X.a' p K (posOf n' y) : ℝ) ∧
      (9 / 10 : ℝ) * X.a ≤ (X.a' p K (posOf n' y) : ℝ) ∧ (X.a' p K (posOf n' y) : ℝ) ≤ 2 * X.a := by
  have hV := hX.valid
  have hr2 := hX.r2
  have hp1 : (1 : ℝ) ≤ p := by have := hX.p13; exact_mod_cast (by omega : 1 ≤ p)
  have hyL := hy
  simp only [Frames.letters, Finset.mem_filter, Finset.mem_Icc] at hy
  obtain ⟨⟨hy1, hy2⟩, hyT⟩ := hy
  have hdeg := hX.degs _ hyT
  have h41y := h41 _ hyT
  have ha'le : (X.a' p K (posOf n' y) : ℝ) ≤ X.deg (posOf n' y) := by
    have h0 : X.a' p K (posOf n' y) ≤ X.deg (posOf n' y) := by
      unfold Dat.a' Dat.d
      rw [if_pos hyT]
      omega
    exact_mod_cast h0
  refine ⟨?_, by linarith [hdeg.1], by linarith [hdeg.2]⟩
  have hwL : X.F.fr (j - 1) 0 ∈ X.F.letters j := by
    simp only [Frames.letters, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨le_refl _, ?_⟩, (hV.2.2.2.2.1 (j - 1) 0 (by omega)).1⟩
    have hg := hV.2.2.2.1 (j - 1)
    rw [sub_add_cancel] at hg
    have h1 := fr_le_fr_of_le hV (j - 1) (r - 1) (by omega)
    have h2 := fr_le_fr_of_le hV j (r - 1) (by omega)
    omega
  have hdist : X.F.dist j y ≤ X.F.dist j (X.F.fr (j - 1) 0) := by
    unfold Frames.dist
    exact Int.toNat_le_toNat (by omega)
  have hQ0 : (p : ℝ) ^ X.F.dist j (X.F.fr (j - 1) 0) ≤ X.Q := hX.twist j _ hwL
  have hQ1 : 1 ≤ X.Q := (one_le_pow₀ hp1).trans hQ0
  have hY := hX.Y1
  have hNs : (6 : ℝ) ≤ X.Ns := by exact_mod_cast six_le_Ns hX
  have hk1 : (1 : ℝ) ≤ ((r + K : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ r + K)
  have hE : (1 : ℝ) ≤ (X.E₀ : ℝ) + X.mStar + 1 := by
    have h1 : (0 : ℝ) ≤ X.E₀ := Nat.cast_nonneg _
    have h2 : (0 : ℝ) ≤ X.mStar := Nat.cast_nonneg _
    linarith
  have hkdef : Dat.k (r := r) K = ((r + K : ℕ) : ℝ) := rfl
  set D0 := X.F.dist j (X.F.fr (j - 1) 0) with hD0
  set Dn := 8 * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) * (p : ℝ) ^ D0 with hDnd
  have hYk : 0 ≤ X.Y * ((r + K : ℕ) : ℝ) ^ 2 * X.Ns :=
    mul_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) (Nat.cast_nonneg _)
  have hDn : 0 < Dn := by
    rw [hDnd, hkdef]
    have h1 : (0 : ℝ) < (p : ℝ) ^ D0 := pow_pos (by linarith) _
    have h2 : (0 : ℝ) < X.Y * ((r + K : ℕ) : ℝ) ^ 2 * X.Ns := by
      have h3 : (0 : ℝ) < ((r + K : ℕ) : ℝ) ^ 2 := by positivity
      have h4 : (0 : ℝ) < X.Ns := by linarith
      have h5 : (0 : ℝ) < X.Y := by linarith
      positivity
    nlinarith
  have hDa : Dn ≤ X.a := by
    have h1 : (8 : ℝ) ≤ 32 * p := by linarith
    have h2 : (p : ℝ) ^ D0 ≤ X.Q ^ 2 * ((X.E₀ : ℝ) + X.mStar + 1) := by
      nlinarith [mul_le_mul_of_nonneg_left hE (sq_nonneg X.Q)]
    have h3 := mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 (by positivity) (by linarith)) hYk
    calc Dn = 8 * (p : ℝ) ^ D0 * (X.Y * ((r + K : ℕ) : ℝ) ^ 2 * X.Ns) := by rw [hDnd, hkdef]; ring
      _ ≤ 32 * p * (X.Q ^ 2 * ((X.E₀ : ℝ) + X.mStar + 1)) * (X.Y * ((r + K : ℕ) : ℝ) ^ 2 * X.Ns) := h3
      _ = 32 * (p : ℝ) * X.Y * ((r + K : ℕ) : ℝ) ^ 2 * (X.Ns : ℝ) * X.Q ^ 2 *
          ((X.E₀ : ℝ) + X.mStar + 1) := by ring
      _ ≤ X.a := hX.P3
  have hfl1 : ⌊X.a / Dn⌋₊ ≠ 0 := by
    have h1 : 1 ≤ ⌊X.a / Dn⌋₊ := Nat.le_floor (by rw [Nat.cast_one, le_div_iff₀ hDn]; linarith)
    omega
  have hRjdef : X.Rj p K j = Nat.log p ⌊X.a / Dn⌋₊ := rfl
  have hRj : (p : ℝ) ^ (X.Rj p K j) ≤ X.a / Dn := by
    have h1 : p ^ (X.Rj p K j) ≤ ⌊X.a / Dn⌋₊ := by rw [hRjdef]; exact Nat.pow_log_le_self p hfl1
    calc (p : ℝ) ^ (X.Rj p K j) = ((p ^ X.Rj p K j : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (⌊X.a / Dn⌋₊ : ℝ) := by exact_mod_cast h1
      _ ≤ X.a / Dn := Nat.floor_le (div_nonneg (by linarith) hDn.le)
  have hpd : (p : ℝ) ^ (X.F.dist j y) ≤ (p : ℝ) ^ D0 := pow_le_pow_right₀ hp1 hdist
  have hA : 0 ≤ (36 / 5 : ℝ) * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) := by
    rw [hkdef]
    have := hYk
    nlinarith
  have e : (36 / 5 : ℝ) * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) * (p : ℝ) ^ (X.F.dist j y + X.Rj p K j) ≤
      (9 / 10) * X.a := by
    rw [pow_add]
    calc (36 / 5 : ℝ) * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) * ((p : ℝ) ^ X.F.dist j y * (p : ℝ) ^ X.Rj p K j)
        ≤ (36 / 5 : ℝ) * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) * ((p : ℝ) ^ D0 * (X.a / Dn)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hpd hRj (by positivity) (by positivity)) hA
      _ = (9 / 10) * X.a := by
          have hk0 : Dat.k (r := r) K ≠ 0 := by rw [hkdef]; linarith
          have hY0 : X.Y ≠ 0 := by linarith
          have hN0 : (X.Ns : ℝ) ≠ 0 := by linarith
          have hpD : (p : ℝ) ^ D0 ≠ 0 := pow_ne_zero _ (by linarith)
          rw [hDnd]
          field_simp
          ring
  linarith [hdeg.1, h41y]

theorem Bdeg_bounds (hX : X.Hyp p K) (hk : 1088 ≤ X.Ck)
    (h41 : ∀ t ∈ X.F.TT, (9 / 10 : ℝ) * (X.deg t : ℝ) ≤ (X.a' p K t : ℝ))
    (j : ℤ) (b : ℤ → ℕ) (hA : X.AdmLL p K j b) (x : ℤ) (hx : x ∈ X.F.letters j) (hlt : x < X.F.fr j 0) :
    (X.a' p K (posOf n' x) : ℝ) / (p : ℝ) ^ (X.F.dist j x + X.Rj p K j) - 2 * Dat.k (r := r) K * (X.Ns : ℝ) ≤
        (X.Bdeg p K j (X.restr j b) x : ℝ) ∧
      (X.Bdeg p K j (X.restr j b) x : ℝ) ≤
        (X.a' p K (posOf n' x) : ℝ) / (p : ℝ) ^ (X.F.dist j x + X.Rj p K j) := by
  have hV := hX.valid
  have hr2 := hX.r2
  have hNs : (6 : ℝ) ≤ X.Ns := by exact_mod_cast six_le_Ns hX
  have hkdef : Dat.k (r := r) K = ((r + K : ℕ) : ℝ) := rfl
  have hpp : 0 < p ^ (X.F.dist j x + X.Rj p K j) := pow_pos hX.prime.pos _
  have hPc : ((p ^ (X.F.dist j x + X.Rj p K j) : ℕ) : ℝ) = (p : ℝ) ^ (X.F.dist j x + X.Rj p K j) := by
    push_cast
    ring
  have hP0 : (0 : ℝ) < (p : ℝ) ^ (X.F.dist j x + X.Rj p K j) := by rw [← hPc]; exact_mod_cast hpp
  unfold Dat.Bdeg
  by_cases hW : X.F.IsW j x
  · rw [if_pos hW]
    unfold Dat.Bw Dat.m0
    set A := X.a' p K (posOf n' x) with hAdef
    set pp := p ^ (X.F.dist j x + X.Rj p K j) with hppdef
    have hq1 : ((A / pp : ℕ) : ℝ) ≤ (A : ℝ) / (pp : ℝ) := Nat.cast_div_le
    have hq2 : (A : ℝ) / (pp : ℝ) < ((A / pp : ℕ) : ℝ) + 1 := by
      have hmod := Nat.div_add_mod A pp
      have hlt := Nat.mod_lt A hpp
      have hppR : (0 : ℝ) < (pp : ℝ) := by exact_mod_cast hpp
      rw [div_lt_iff₀ hppR]
      have e1 : (A : ℝ) = (pp : ℝ) * ((A / pp : ℕ) : ℝ) + ((A % pp : ℕ) : ℝ) := by exact_mod_cast hmod.symm
      have e2 : ((A % pp : ℕ) : ℝ) < (pp : ℝ) := by exact_mod_cast hlt
      nlinarith
    rw [← hPc]
    set z : ℤ := ((A / pp : ℕ) : ℤ) - ((r + K + r + 1 : ℕ) : ℤ) - (((r + K) * X.Ns + 1 : ℕ) : ℤ) with hz
    have hzR : (z : ℝ) = ((A / pp : ℕ) : ℝ) - ((r + K + r + 1 : ℕ) : ℝ) - (((r + K) * X.Ns + 1 : ℕ) : ℝ) := by
      simp only [hz, Int.cast_sub, Int.cast_natCast]
    have hc1 : ((r + K + r + 1 : ℕ) : ℝ) = 2 * (r : ℝ) + K + 1 := by push_cast; ring
    have hc2 : (((r + K) * X.Ns + 1 : ℕ) : ℝ) = ((r : ℝ) + K) * X.Ns + 1 := by push_cast; ring
    rw [hc1, hc2] at hzR
    have hzt1 : (z : ℝ) ≤ ((z.toNat : ℕ) : ℝ) := by
      have h1 : z ≤ (z.toNat : ℤ) := Int.self_le_toNat z
      exact_mod_cast h1
    have hzt2 : ((z.toNat : ℕ) : ℝ) ≤ max (z : ℝ) 0 := by
      rcases le_or_gt 0 z with h | h
      · have h1 : ((z.toNat : ℕ) : ℤ) = z := Int.toNat_of_nonneg h
        have h2 : ((z.toNat : ℕ) : ℝ) = (z : ℝ) := by exact_mod_cast h1
        rw [h2]
        exact le_max_left _ _
      · rw [Int.toNat_of_nonpos h.le]
        simp
    have hApos : (0 : ℝ) ≤ (A : ℝ) / (pp : ℝ) := by positivity
    have hkc : ((r + K : ℕ) : ℝ) = (r : ℝ) + K := by push_cast; ring
    rw [hkdef, hkc]
    have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr2
    have hKR : (0 : ℝ) ≤ K := Nat.cast_nonneg _
    have hprod : ((r : ℝ) + K) * 6 ≤ ((r : ℝ) + K) * X.Ns :=
      mul_le_mul_of_nonneg_left hNs (by linarith)
    constructor
    · linarith
    · have h1 : max (z : ℝ) 0 ≤ (A : ℝ) / (pp : ℝ) := by
        apply max_le
        · rw [hzR]
          have h2 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg _
          have h3 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg _
          have h4 : (0 : ℝ) ≤ ((r : ℝ) + K) * X.Ns := by positivity
          linarith
        · exact hApos
      linarith
  · rw [if_neg hW]
    have hxl := hx
    simp only [Frames.letters, Finset.mem_filter, Finset.mem_Icc] at hxl
    have hlate : x ∈ X.toLate j := by
      unfold Dat.toLate
      simp only [Finset.mem_filter]
      exact ⟨hx, hW⟩
    unfold Dat.restr
    rw [if_pos hlate]
    have hLL : x ∈ X.F.LLset j := by
      simp only [Frames.LLset, Finset.mem_filter, Finset.mem_Ioo]
      unfold Frames.IsW at hW
      push_neg at hW
      exact ⟨⟨hW, hlt⟩, hxl.2⟩
    obtain ⟨h1, h2⟩ := hA x hLL
    have hPz : ((X.Pz p K j x : ℕ) : ℝ) = (p : ℝ) ^ (X.F.dist j x + X.Rj p K j) := by
      unfold Dat.Pz
      push_cast
      ring
    rw [hPz] at h1 h2
    rw [hkdef] at h1 ⊢
    have h3 : (0 : ℝ) ≤ ((r + K : ℕ) : ℝ) := Nat.cast_nonneg _
    have h4 : ((r + K : ℕ) : ℝ) ≤ 2 * ((r + K : ℕ) : ℝ) * (X.Ns : ℝ) := by nlinarith
    constructor
    · linarith
    · exact h2

end Num61

end Formalism.MainNotions.SelectionLemmas.Pf.TE
