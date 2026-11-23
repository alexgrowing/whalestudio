import Mathlib

noncomputable section

open Matrix
open scoped BigOperators Pointwise

namespace Formalism.L2.SG.Pf.Unip

section Pat

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K]

def InPat (lv : ι → ℕ) (k : ℕ) (Z : Matrix ι ι K) : Prop := ∀ i j, lv j < lv i + k → Z i j = 0

variable {lv : ι → ℕ} {k l : ℕ} {Z W : Matrix ι ι K}

theorem inPat_zero (k : ℕ) : InPat lv k (0 : Matrix ι ι K) := by
  intro i j _
  simp

theorem inPat_add (hZ : InPat lv k Z) (hW : InPat lv k W) : InPat lv k (Z + W) := by
  intro i j h
  simp [hZ i j h, hW i j h]

theorem inPat_sub (hZ : InPat lv k Z) (hW : InPat lv k W) : InPat lv k (Z - W) := by
  intro i j h
  simp [hZ i j h, hW i j h]

theorem inPat_neg (hZ : InPat lv k Z) : InPat lv k (-Z) := by
  intro i j h
  simp [hZ i j h]

theorem inPat_smul (c : K) (hZ : InPat lv k Z) : InPat lv k (c • Z) := by
  intro i j h
  simp [hZ i j h]

theorem inPat_mono (hkl : k ≤ l) (hZ : InPat lv l Z) : InPat lv k Z := fun i j h => hZ i j (by omega)

theorem inPat_one : InPat lv 0 (1 : Matrix ι ι K) := by
  intro i j h
  have hij : i ≠ j := by
    rintro rfl
    omega
  exact Matrix.one_apply_ne hij

theorem inPat_mul (hZ : InPat lv k Z) (hW : InPat lv l W) : InPat lv (k + l) (Z * W) := by
  intro i j h
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun m _ => ?_
  by_cases h1 : lv m < lv i + k
  · rw [hZ i m h1, zero_mul]
  · rw [hW m j (by omega), mul_zero]

theorem inPat_pow (hZ : InPat lv k Z) (m : ℕ) : InPat lv (k * m) (Z ^ m) := by
  induction m with
  | zero =>
    rw [pow_zero, Nat.mul_zero]
    exact inPat_one
  | succ m ih =>
    rw [pow_succ, mul_add_one]
    exact inPat_mul ih hZ

theorem inPat_sum {α : Type*} {s : Finset α} {f : α → Matrix ι ι K} (h : ∀ a ∈ s, InPat lv k (f a)) :
    InPat lv k (∑ a ∈ s, f a) := by
  intro i j hij
  rw [Matrix.sum_apply]
  exact Finset.sum_eq_zero fun a ha => h a ha i j hij

theorem eq_zero_of_inPat {L : ℕ} (hL : ∀ i, lv i < L) (hZ : InPat lv L Z) : Z = 0 := by
  ext i j
  have := hL j
  exact hZ i j (by omega)

theorem pow_eq_zero_of_inPat {L : ℕ} (hk : 1 ≤ k) (hL : ∀ i, lv i < L) (hZ : InPat lv k Z) : Z ^ L = 0 := eq_zero_of_inPat hL (inPat_mono (by nlinarith) (inPat_pow hZ L))

theorem inPat_map {K' : Type*} [CommRing K'] (f : K →+* K') (hZ : InPat lv k Z) : InPat lv k (Z.map f) := by
  intro i j h
  simp [Matrix.map_apply, hZ i j h]

end Pat

section Sharp

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] [StarRing K]

def Graded (lv : ι → ℕ) (T : ℕ) (J : Matrix ι ι K) : Prop := ∀ i j, J i j ≠ 0 → lv i + lv j = T

variable {lv : ι → ℕ} {T k : ℕ}

def sharp (J J' M : Matrix ι ι K) : Matrix ι ι K := J' * Mᴴ * J

theorem inPat_sharp {J J' Z : Matrix ι ι K} (hJ : Graded lv T J) (hJ' : Graded lv T J') (hZ : InPat lv k Z) :
    InPat lv k (sharp J J' Z) := by
  intro i j hij
  unfold sharp
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun b _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [Matrix.conjTranspose_apply]
  by_cases ha : J' i a = 0
  · simp [ha]
  by_cases hb : J b j = 0
  · simp [hb]
  have e1 := hJ' i a ha
  have e2 := hJ b j hb
  rw [hZ b a (by omega), star_zero, mul_zero, zero_mul]

variable {J J' : Matrix ι ι K}

theorem sharp_add (M N : Matrix ι ι K) : sharp J J' (M + N) = sharp J J' M + sharp J J' N := by
  simp only [sharp, conjTranspose_add, Matrix.mul_add, Matrix.add_mul]

theorem sharp_sub (M N : Matrix ι ι K) : sharp J J' (M - N) = sharp J J' M - sharp J J' N := by
  simp only [sharp, conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul]

theorem sharp_neg (M : Matrix ι ι K) : sharp J J' (-M) = -sharp J J' M := by
  simp only [sharp, conjTranspose_neg, Matrix.mul_neg, Matrix.neg_mul]

theorem sharp_smul (c : K) (M : Matrix ι ι K) : sharp J J' (c • M) = star c • sharp J J' M := by
  simp only [sharp, conjTranspose_smul, mul_smul_comm, smul_mul_assoc]

theorem sharp_one (h : J' * J = 1) : sharp J J' (1 : Matrix ι ι K) = 1 := by
  simp only [sharp, conjTranspose_one, Matrix.mul_one, h]

theorem mul_comm_one {M N : Matrix ι ι K} (h : M * N = 1) : N * M = 1 := by
  first
  | exact mul_eq_one_comm.mp h
  | exact (by
      rw [← Matrix.inv_eq_right_inv h]
      exact Matrix.nonsing_inv_mul M (Matrix.isUnit_det_of_right_inverse h))

theorem sharp_mul_self (h : J' * J = 1) {M : Matrix ι ι K} (hM : Mᴴ * J * M = J) : sharp J J' M * M = 1 := by
  unfold sharp
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Mᴴ, hM, h]

theorem self_mul_sharp (h : J' * J = 1) {M : Matrix ι ι K} (hM : Mᴴ * J * M = J) : M * sharp J J' M = 1 := mul_comm_one (sharp_mul_self h hM)

theorem sharp_of_skew (h : J' * J = 1) {X : Matrix ι ι K} (hX : Xᴴ * J = -(J * X)) : sharp J J' X = -X := by
  unfold sharp
  rw [Matrix.mul_assoc, hX, Matrix.mul_neg, ← Matrix.mul_assoc, h, Matrix.one_mul]

variable [Invertible (2 : K)]

theorem star_half : star (⅟2 : K) = ⅟2 := by
  have h2 : (2 : K) * star (⅟2 : K) = 1 := by
    have := congrArg star (invOf_mul_self (2 : K))
    rw [star_mul, star_one, star_ofNat] at this
    exact this
  exact (invOf_eq_right_inv h2).symm

theorem half_add_half (M : Matrix ι ι K) : (⅟2 : K) • M + (⅟2 : K) • M = M := by
  rw [← add_smul, invOf_two_add_invOf_two, one_smul]

def proj (J J' M : Matrix ι ι K) : Matrix ι ι K := (⅟2 : K) • (M - sharp J J' M)

theorem inPat_proj (hJ : Graded lv T J) (hJ' : Graded lv T J') {M : Matrix ι ι K} (hM : InPat lv k M) :
    InPat lv k (proj J J' M) := by
  unfold proj
  exact inPat_smul _ (inPat_sub hM (inPat_sharp hJ hJ' hM))

theorem proj_skew (hJh : Jᴴ = J) (hJ'h : J'ᴴ = J') (h : J' * J = 1) (h' : J * J' = 1) (M : Matrix ι ι K) :
    (proj J J' M)ᴴ * J = -(J * proj J J' M) := by
  have e1 : (M - J' * Mᴴ * J)ᴴ * J = -(J * (M - J' * Mᴴ * J)) := by
    have a : J * (M * J') * J = J * M := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, h, Matrix.mul_one]
    have b : J * (J' * Mᴴ * J) = Mᴴ * J := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h', Matrix.one_mul]
    rw [conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hJh, hJ'h,
      Matrix.sub_mul, Matrix.mul_sub, a, b, neg_sub]
  unfold proj sharp
  rw [conjTranspose_smul, star_half, smul_mul_assoc, mul_smul_comm, e1, smul_neg]

theorem proj_of_skew (h : J' * J = 1) {X : Matrix ι ι K} (hX : Xᴴ * J = -(J * X)) :
    proj J J' X = X := by
  unfold proj
  rw [sharp_of_skew h hX, sub_neg_eq_add, smul_add, half_add_half]

theorem sub_proj_of_unitary (hJ : Graded lv T J) (hJ' : Graded lv T J') (h : J' * J = 1)
    {x : Matrix ι ι K} (hx : xᴴ * J * x = J) (hx1 : InPat lv k (x - 1)) :
    InPat lv (k + k) ((x - 1) - proj J J' (x - 1)) := by
  obtain ⟨Z, rfl⟩ : ∃ Z, x = Z + 1 := ⟨x - 1, (sub_add_cancel x 1).symm⟩
  rw [add_sub_cancel_right] at hx1 ⊢
  have hA : InPat lv k (sharp J J' Z) := inPat_sharp hJ hJ' hx1
  have h0 := sharp_mul_self h hx
  rw [sharp_add, sharp_one h] at h0
  have e : sharp J J' Z * Z + sharp J J' Z + Z = 0 := by
    have t : sharp J J' Z * Z + sharp J J' Z + Z
        = (sharp J J' Z + 1) * (Z + 1) - 1 := by noncomm_ring
    rw [t, h0, sub_self]
  have hz : -(sharp J J' Z * Z) = sharp J J' Z + Z :=
    neg_eq_iff_add_eq_zero.mpr (by rw [← add_assoc]; exact e)
  have key : Z - proj J J' Z = (⅟2 : K) • -(sharp J J' Z * Z) := by
    rw [hz, proj, smul_sub, smul_add]
    calc Z - ((⅟2 : K) • Z - (⅟2 : K) • sharp J J' Z)
        = ((⅟2 : K) • Z + (⅟2 : K) • Z) - ((⅟2 : K) • Z - (⅟2 : K) • sharp J J' Z) := by
          rw [half_add_half]
      _ = (⅟2 : K) • sharp J J' Z + (⅟2 : K) • Z := by abel
  rw [key]
  exact inPat_smul _ (inPat_neg (inPat_mul hA hx1))

end Sharp

section Cay

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] [Invertible (2 : K)]

def geo (N : ℕ) (Y : Matrix ι ι K) : Matrix ι ι K := ∑ j ∈ Finset.range N, Y ^ j

def cay (N : ℕ) (Z : Matrix ι ι K) : Matrix ι ι K := 1 + Z * geo N ((⅟2 : K) • Z)

variable {lv : ι → ℕ} {k : ℕ}

theorem inPat_geo {Z : Matrix ι ι K} (hZ : InPat lv k Z) (N : ℕ) : InPat lv 0 (geo N Z) := by
  unfold geo
  exact inPat_sum fun j _ => inPat_mono (Nat.zero_le _) (inPat_pow hZ j)

theorem geo_succ (N : ℕ) (Y : Matrix ι ι K) : geo (N + 1) Y = Y * geo N Y + 1 := by
  unfold geo
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp only [pow_succ', pow_zero]

theorem cay_sub (N : ℕ) {Z : Matrix ι ι K} (hZ : InPat lv k Z) : InPat lv (k + k) (cay (N + 1) Z - 1 - Z) := by
  unfold cay
  rw [geo_succ, add_sub_cancel_left, Matrix.mul_add, Matrix.mul_one, add_sub_cancel_right]
  have := inPat_mul hZ (inPat_mul (inPat_smul (⅟2 : K) hZ)
    (inPat_geo (inPat_smul (⅟2 : K) hZ) N))
  rwa [Nat.add_zero] at this

theorem cay_sub_one (N : ℕ) {Z : Matrix ι ι K} (hZ : InPat lv k Z) : InPat lv k (cay N Z - 1) := by
  unfold cay
  rw [add_sub_cancel_left]
  have := inPat_mul hZ (inPat_geo (inPat_smul (⅟2 : K) hZ) N)
  rwa [Nat.add_zero] at this

theorem cay_map {K' : Type*} [CommRing K'] [Invertible (2 : K')] (f : K →+* K') (N : ℕ) (Z : Matrix ι ι K) :
    (cay N Z).map f = cay N (Z.map f) := by
  have h2 : f (⅟2 : K) = ⅟2 := by
    refine (invOf_eq_right_inv ?_).symm
    rw [← map_ofNat f 2, ← map_mul, mul_invOf_self, map_one]
  have hm : ∀ M : Matrix ι ι K, M.map f = f.mapMatrix M := fun _ => rfl
  have hs : f.mapMatrix ((⅟2 : K) • Z) = (⅟2 : K') • f.mapMatrix Z := by
    ext a b
    simp [h2]
  unfold cay geo
  rw [hm, hm, map_add, map_one, map_mul, map_sum]
  simp only [map_pow, hs]

theorem cay_continuous (N : ℕ) {ι' : Type*} [Fintype ι'] [DecidableEq ι'] :
    Continuous fun Z : Matrix ι' ι' ℂ => cay N Z := by
  unfold cay geo
  first
  | fun_prop
  | exact continuous_const.add (continuous_id.mul
      (continuous_finset_sum _ fun j _ => (continuous_const.smul continuous_id).pow j))

variable [StarRing K]

theorem cay_unitary {J : Matrix ι ι K} {N : ℕ} {Z : Matrix ι ι K} (hZ : Zᴴ * J = -(J * Z))
    (hN : ((⅟2 : K) • Z) ^ N = 0) : (cay N Z)ᴴ * J * cay N Z = J := by
  obtain ⟨Y, hYdef⟩ : ∃ Y, Y = (⅟2 : K) • Z := ⟨_, rfl⟩
  rw [← hYdef] at hN
  have hZY : Z = Y + Y := by
    rw [hYdef]
    exact (half_add_half Z).symm
  have hY : Yᴴ * J = -(J * Y) := by
    rw [hYdef, conjTranspose_smul, star_half, smul_mul_assoc, hZ, mul_smul_comm, smul_neg]
  have hpow : ∀ j : ℕ, Yᴴ ^ j * J = J * (-Y) ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', Matrix.mul_assoc, ih, ← Matrix.mul_assoc, hY, pow_succ', ← Matrix.mul_assoc,
        Matrix.mul_neg, Matrix.neg_mul]
  have hS : (geo N Y)ᴴ * J = J * geo N (-Y) := by
    unfold geo
    rw [conjTranspose_sum, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [conjTranspose_pow, hpow]
  have h1 : (1 - Y) * geo N Y = 1 := by
    unfold geo
    rw [mul_neg_geom_sum, hN, sub_zero]
  have hN' : (-Y) ^ N = 0 := by rw [neg_pow, hN, mul_zero]
  have h2 : geo N (-Y) * (1 + Y) = 1 := by
    unfold geo
    have := geom_sum_mul_neg (-Y) N
    rw [sub_neg_eq_add, hN', sub_zero] at this
    exact this
  have hS1 : geo N Y = 1 + Y * geo N Y := by
    have := h1
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_iff_eq_add] at this
    exact this
  have hC : cay N Z = 1 + Z * geo N Y := by
    rw [hYdef]
    rfl
  have hC2 : cay N Z = (1 + Y) * geo N Y := by
    rw [hC, hZY, Matrix.add_mul, Matrix.add_mul, Matrix.one_mul]
    calc 1 + (Y * geo N Y + Y * geo N Y) = (1 + Y * geo N Y) + Y * geo N Y := by abel
      _ = geo N Y + Y * geo N Y := by rw [← hS1]
  have hA : (1 + Y)ᴴ * J = J * (1 - Y) := by
    rw [conjTranspose_add, conjTranspose_one, Matrix.add_mul, Matrix.one_mul, hY, Matrix.mul_sub,
      Matrix.mul_one, sub_eq_add_neg]
  have hcomm : (1 - Y) * (1 + Y) = (1 + Y) * (1 - Y) := by noncomm_ring
  rw [hC2, conjTranspose_mul]
  calc (geo N Y)ᴴ * (1 + Y)ᴴ * J * ((1 + Y) * geo N Y)
      = (geo N Y)ᴴ * ((1 + Y)ᴴ * J) * ((1 + Y) * geo N Y) := by simp only [Matrix.mul_assoc]
    _ = ((geo N Y)ᴴ * J) * ((1 - Y) * (1 + Y)) * geo N Y := by
      rw [hA]; simp only [Matrix.mul_assoc]
    _ = J * (geo N (-Y) * (1 + Y)) * ((1 - Y) * geo N Y) := by
      rw [hS, hcomm]; simp only [Matrix.mul_assoc]
    _ = J := by rw [h2, h1, Matrix.mul_one, Matrix.mul_one]

end Cay

section Step

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K]

variable {lv : ι → ℕ} {k : ℕ}

theorem filtered_mul_mul_sub_sub {a b c : Matrix ι ι K} (ha : InPat lv k (a - 1)) (hb : InPat lv k (b - 1))
    (hc : InPat lv k (c - 1)) : InPat lv (k + k) (a * b * c - 1 - ((a - 1) + (b - 1) + (c - 1))) := by
  obtain ⟨A, rfl⟩ : ∃ A, a = 1 + A := ⟨a - 1, by abel⟩
  obtain ⟨B, rfl⟩ : ∃ B, b = 1 + B := ⟨b - 1, by abel⟩
  obtain ⟨C, rfl⟩ : ∃ C, c = 1 + C := ⟨c - 1, by abel⟩
  simp only [add_sub_cancel_left] at ha hb hc ⊢
  have e : (1 + A) * (1 + B) * (1 + C) - 1 - (A + B + C) = A * B + A * C + B * C + A * B * C := by
    noncomm_ring
  rw [e]
  exact inPat_add (inPat_add (inPat_add (inPat_mul ha hb) (inPat_mul ha hc))
    (inPat_mul hb hc)) (inPat_mono (by omega) (inPat_mul (inPat_mul ha hb) hc))

variable [StarRing K] [Invertible (2 : K)] {T : ℕ} {J J' : Matrix ι ι K}

theorem sharp_cay_sub (hJ : Graded lv T J) (hJ' : Graded lv T J') (h : J' * J = 1) (N : ℕ)
    {W : Matrix ι ι K} (hW : InPat lv k W) :
    InPat lv (k + k) (sharp J J' (cay (N + 1) W) - 1 - sharp J J' W) := by
  have e : sharp J J' (cay (N + 1) W) - 1 - sharp J J' W
      = sharp J J' (cay (N + 1) W - 1 - W) := by
    rw [sharp_sub, sharp_sub, sharp_one h]
  rw [e]
  exact inPat_sharp hJ hJ' (cay_sub N hW)

theorem sharp_cay_sub_one (hJ : Graded lv T J) (hJ' : Graded lv T J') (h : J' * J = 1) (N : ℕ)
    {W : Matrix ι ι K} (hW : InPat lv k W) : InPat lv k (sharp J J' (cay N W) - 1) := by
  have e : sharp J J' (cay N W) - 1 = sharp J J' (cay N W - 1) := by
    rw [sharp_sub, sharp_one h]
  rw [e]
  exact inPat_sharp hJ hJ' (cay_sub_one N hW)

theorem step_mat (hJ : Graded lv T J) (hJ' : Graded lv T J') (hJh : Jᴴ = J) (hJ'h : J'ᴴ = J')
    (h : J' * J = 1) (h' : J * J' = 1) (N : ℕ) {x Y : Matrix ι ι K} (hx : xᴴ * J * x = J)
    (hx1 : InPat lv k (x - 1)) (hY : InPat lv k Y) (hYs : Yᴴ * J = -(J * Y)) :
    InPat lv (k + k) (sharp J J' (cay (N + 1) Y) * x *
      sharp J J' (cay (N + 1) (proj J J' (x - 1) - Y)) - 1) := by
  have hSf : InPat lv k (proj J J' (x - 1)) := inPat_proj hJ hJ' hx1
  have hSY : InPat lv k (proj J J' (x - 1) - Y) := inPat_sub hSf hY
  have hAS : sharp J J' (proj J J' (x - 1)) = -proj J J' (x - 1) :=
    sharp_of_skew h (proj_skew hJh hJ'h h h' (x - 1))
  have t1 := sharp_cay_sub hJ hJ' h N hY
  have t2 := sharp_cay_sub hJ hJ' h N hSY
  have t3 := sub_proj_of_unitary hJ hJ' h hx hx1
  have t4 := filtered_mul_mul_sub_sub (sharp_cay_sub_one hJ hJ' h (N + 1) hY) hx1
    (sharp_cay_sub_one hJ hJ' h (N + 1) hSY)
  have key := inPat_add (inPat_add (inPat_add t4 t1) t2) t3
  rw [sharp_sub, hAS] at key
  convert key using 1
  abel

end Step

section Cover

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem cover_of_steps (Γ : Set G) (hΓ : ∀ a ∈ Γ, ∀ b ∈ Γ, a * b ∈ Γ) (h1 : (1 : G) ∈ Γ)
    (R : ℕ → Set G) (m : ℕ) (hm : ∀ x ∈ R m, x = 1) (S : ℕ → Set G) (hS : ∀ k, IsCompact (S k))
    (hstep : ∀ k < m, ∀ x ∈ R k, ∃ γ ∈ Γ, ∃ y ∈ R (k + 1), ∃ s ∈ S k, x = γ * y * s) :
    ∃ C : Set G, IsCompact C ∧ ∀ x ∈ R 0, ∃ γ ∈ Γ, ∃ c ∈ C, x = γ * c := by
  have main : ∀ n k, k + n = m →
      ∃ C : Set G, IsCompact C ∧ ∀ x ∈ R k, ∃ γ ∈ Γ, ∃ c ∈ C, x = γ * c := by
    intro n
    induction n with
    | zero =>
      intro k hk
      have hkm : k = m := by omega
      subst hkm
      refine ⟨{1}, isCompact_singleton, fun x hx => ⟨1, h1, 1, Set.mem_singleton 1, ?_⟩⟩
      rw [hm x hx, one_mul]
    | succ n ih =>
      intro k hk
      obtain ⟨C, hC, hCx⟩ := ih (k + 1) (by omega)
      refine ⟨C * S k, hC.mul (hS k), fun x hx => ?_⟩
      obtain ⟨γ, hγ, y, hy, s, hs, rfl⟩ := hstep k (by omega) x hx
      obtain ⟨γ', hγ', c, hc, rfl⟩ := hCx y hy
      exact ⟨γ * γ', hΓ _ hγ _ hγ', c * s, Set.mul_mem_mul hc hs, by simp only [mul_assoc]⟩
  exact main m 0 (zero_add m)

end Cover

end Formalism.L2.SG.Pf.Unip
