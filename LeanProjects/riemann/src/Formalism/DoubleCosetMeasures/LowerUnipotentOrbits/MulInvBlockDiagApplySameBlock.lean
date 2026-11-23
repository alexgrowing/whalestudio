import Formalism.DoubleCosetMeasures.Statement

set_option maxHeartbeats 400000

noncomputable section

open Matrix

namespace Formalism.DoubleCosetMeasures.P

open Formalism.DoubleCosetMeasures

namespace Phase

theorem revIn_lt : ∀ (s : List ℕ) (j : ℕ), j < s.sum → revIn s j < s.sum
  | [], j, h => by simpa [revIn] using h
  | a :: s, j, h => by
    simp only [revIn, List.sum_cons] at h ⊢
    split_ifs with hj
    · omega
    · have := revIn_lt s (j - a) (by omega); omega

theorem revIn_revIn : ∀ (s : List ℕ) (j : ℕ), j < s.sum → revIn s (revIn s j) = j
  | [], j, _ => by simp [revIn]
  | a :: s, j, h => by
    simp only [List.sum_cons] at h
    by_cases hj : j < a
    · simp only [revIn, if_pos hj]
      rw [if_pos (by omega)]; omega
    · simp only [revIn, if_neg hj]
      rw [if_neg (by omega)]
      have e : a + revIn s (j - a) - a = revIn s (j - a) := by omega
      rw [e, revIn_revIn s (j - a) (by omega)]; omega

theorem blk_revIn : ∀ (s : List ℕ) (j : ℕ), j < s.sum → blk s (revIn s j) = blk s j
  | [], j, _ => by simp [blk]
  | a :: s, j, h => by
    simp only [List.sum_cons] at h
    by_cases hj : j < a
    · simp only [revIn, blk, if_pos hj]
      rw [if_pos (by omega)]
    · simp only [revIn, blk, if_neg hj]
      rw [if_neg (by omega)]
      have e : a + revIn s (j - a) - a = revIn s (j - a) := by omega
      rw [e, blk_revIn s (j - a) (by omega)]

theorem blk_mono : ∀ (s : List ℕ) (i j : ℕ), i ≤ j → blk s i ≤ blk s j
  | [], _, _, _ => by simp [blk]
  | a :: s, i, j, h => by
    simp only [blk]
    split_ifs with h1 h2 h2
    · exact le_refl _
    · omega
    · omega
    · have := blk_mono s (i - a) (j - a) (by omega); omega

theorem revIn_anti : ∀ (s : List ℕ) (i j : ℕ), j < s.sum → i < j → blk s i = blk s j →
    revIn s j < revIn s i
  | [], _, _, h, _, _ => by simp at h
  | a :: s, i, j, h, hij, hb => by
    simp only [List.sum_cons] at h
    simp only [blk] at hb
    simp only [revIn]
    split_ifs at hb ⊢ with h1 h2 h2
    · omega
    · omega
    · omega
    · have := revIn_anti s (i - a) (j - a) (by omega) (by omega) (by omega); omega

theorem revIn_succ : ∀ (s : List ℕ) (j : ℕ), j + 1 < s.sum → blk s j = blk s (j + 1) →
    revIn s (j + 1) + 1 = revIn s j
  | [], _, h, _ => by simp at h
  | a :: s, j, h, hb => by
    simp only [List.sum_cons] at h
    simp only [blk] at hb
    simp only [revIn]
    split_ifs at hb ⊢ with h1 h2 h2
    · omega
    · omega
    · omega
    · have e : j + 1 - a = (j - a) + 1 := by omega
      rw [e] at hb ⊢
      have := revIn_succ s (j - a) (by omega) (by omega); omega

def revF (s : List ℕ) (a : Fin s.sum) : Fin s.sum := ⟨revIn s a, revIn_lt s a a.2⟩

@[simp] theorem revF_val (s : List ℕ) (a : Fin s.sum) : (revF s a : ℕ) = revIn s a := rfl

@[simp] theorem revF_revF (s : List ℕ) (a : Fin s.sum) : revF s (revF s a) = a := Fin.ext (revIn_revIn s a a.2)

@[simp] theorem blk_revF (s : List ℕ) (a : Fin s.sum) : blk s (revF s a) = blk s a := blk_revIn s a a.2

theorem revF_inj (s : List ℕ) {a c : Fin s.sum} (h : revF s a = revF s c) : a = c := by
  calc a = revF s (revF s a) := (revF_revF s a).symm
    _ = revF s (revF s c) := by rw [h]
    _ = c := revF_revF s c

theorem revF_lt_of_blk_eq (s : List ℕ) {a c : Fin s.sum} (hb : blk s a = blk s c) (h : a < c) :
    revF s c < revF s a := revIn_anti s a c c.2 h hb

theorem revF_lt_of_blk_lt (s : List ℕ) {a c : Fin s.sum} (hb : blk s a < blk s c) :
    revF s a < revF s c := by
  show revIn s a < revIn s c
  by_contra hcon
  have := blk_mono s (revIn s c) (revIn s a) (by omega)
  rw [blk_revIn s c c.2, blk_revIn s a a.2] at this
  omega

theorem blk_lt_of_lt_of_ne (s : List ℕ) {a c : Fin s.sum} (h : a < c) (hb : blk s a ≠ blk s c) :
    blk s a < blk s c := lt_of_le_of_ne (blk_mono s a c (le_of_lt h)) hb

variable {K : Type} [CommRing K]

def mono (s : List ℕ) (f : Fin s.sum → K) : Matrix (Fin s.sum) (Fin s.sum) K :=
  fun a c => if c = revF s a then f a else 0

theorem mono_mul (s : List ℕ) (f : Fin s.sum → K) (M : Matrix (Fin s.sum) (Fin s.sum) K)
    (a c : Fin s.sum) : (mono s f * M) a c = f a * M (revF s a) c := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (revF s a)]
  · simp [mono]
  · intro b _ hb
    simp only [mono]
    rw [if_neg hb, zero_mul]
  · simp

theorem mul_mono (s : List ℕ) (f : Fin s.sum → K) (M : Matrix (Fin s.sum) (Fin s.sum) K)
    (a c : Fin s.sum) : (M * mono s f) a c = M a (revF s c) * f (revF s c) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (revF s c)]
  · simp [mono]
  · intro b _ hb
    simp only [mono]
    rw [if_neg (fun h => hb (by rw [h, revF_revF])), mul_zero]
  · simp

theorem pt_eq_mono (s : List ℕ) (t : ℕ → Kˣ) :
    pt s t = mono s (fun a => ((t (blk s a) : Kˣ) : K)) := by
  unfold pt
  funext a b
  simp only [mono]
  by_cases h : (b : ℕ) = revIn s a
  · rw [if_pos h, if_pos (Fin.ext h)]
  · rw [if_neg h, if_neg (fun h' => h (congrArg Fin.val h'))]

def ptI (s : List ℕ) (t : ℕ → Kˣ) : Matrix (Fin s.sum) (Fin s.sum) K :=
  mono s (fun a => (((t (blk s a))⁻¹ : Kˣ) : K))

theorem pt_mul_ptI (s : List ℕ) (t : ℕ → Kˣ) : pt s t * ptI s t = (1 : Matrix _ _ K) := by
  rw [pt_eq_mono]
  ext a c
  rw [mono_mul]
  simp only [ptI, mono, revF_revF, blk_revF, Matrix.one_apply]
  by_cases h : c = a
  · subst h; simp
  · simp [h, Ne.symm h]

theorem ptI_mul_pt (s : List ℕ) (t : ℕ → Kˣ) : ptI s t * pt s t = (1 : Matrix _ _ K) := by
  rw [pt_eq_mono]
  ext a c
  rw [ptI, mono_mul]
  simp only [mono, revF_revF, blk_revF, Matrix.one_apply]
  by_cases h : c = a
  · subst h; simp
  · simp [h, Ne.symm h]

theorem conj_apply (s : List ℕ) (t : ℕ → Kˣ) (M : Matrix (Fin s.sum) (Fin s.sum) K)
    (a c : Fin s.sum) : (ptI s t * M * pt s t) a c =
      (((t (blk s a))⁻¹ : Kˣ) : K) * M (revF s a) (revF s c) * ((t (blk s c) : Kˣ) : K) := by
  rw [pt_eq_mono, mul_mono, ptI, mono_mul]
  simp only [blk_revF]

theorem low_zero {n : ℕ} {x : Matrix (Fin n) (Fin n) K} (hx : IsLowUni x) {i j : Fin n}
    (h : i < j) : x i j = 0 := by
  first
  | exact hx.1 h
  | exact hx.1 (show OrderDual.toDual j < OrderDual.toDual i from h)

theorem up_zero {n : ℕ} {y : Matrix (Fin n) (Fin n) K} (hy : IsUpUni y) {i j : Fin n}
    (h : j < i) : y i j = 0 := by
  first
  | exact hy.1 h
  | (unfold IsUpUni at hy; done)

theorem eq_one_of_low_up {n : ℕ} {m : Matrix (Fin n) (Fin n) K} (h1 : IsLowUni m)
    (h2 : IsUpUni m) : m = 1 := by
  ext i j
  rcases lt_trichotomy i j with h | rfl | h
  · rw [low_zero h1 h, Matrix.one_apply_ne h.ne]
  · rw [h1.2 i, Matrix.one_apply_eq]
  · rw [up_zero h2 h, Matrix.one_apply_ne h.ne']

theorem mul_inv_one_low {n : ℕ} {x : Matrix (Fin n) (Fin n) K} (hx : IsLowUni x) :
    x * x⁻¹ = 1 := by
  have hd : IsUnit x.det := by
    rw [Matrix.det_of_isLowerTriangular x hx.1]
    simp [hx.2]
  exact Matrix.mul_nonsing_inv x hd

theorem inv_mul_one_low {n : ℕ} {x : Matrix (Fin n) (Fin n) K} (hx : IsLowUni x) :
    x⁻¹ * x = 1 := by
  have hd : IsUnit x.det := by
    rw [Matrix.det_of_isLowerTriangular x hx.1]
    simp [hx.2]
  exact Matrix.nonsing_inv_mul x hd

theorem mul_inv_one_up {n : ℕ} {x : Matrix (Fin n) (Fin n) K} (hx : IsUpUni x) :
    x * x⁻¹ = 1 := by
  have hd : IsUnit x.det := by
    rw [Matrix.det_of_isUpperTriangular hx.1]
    simp [hx.2]
  exact Matrix.mul_nonsing_inv x hd

theorem inv_mul_one_up {n : ℕ} {x : Matrix (Fin n) (Fin n) K} (hx : IsUpUni x) :
    x⁻¹ * x = 1 := by
  have hd : IsUnit x.det := by
    rw [Matrix.det_of_isUpperTriangular hx.1]
    simp [hx.2]
  exact Matrix.nonsing_inv_mul x hd

theorem simple_add_zero {n : ℕ} {y z : Matrix (Fin n) (Fin n) K} (hy : IsUpUni y)
    (hz : IsUpUni z) (hyz : y * z = 1) (j k : Fin n) (hk : (k : ℕ) = j + 1) :
    y j k + z j k = 0 := by
  have hjk : j ≠ k := by
    intro h'
    rw [h'] at hk
    omega
  have h := congrFun (congrFun hyz j) k
  rw [Matrix.mul_apply, Matrix.one_apply_ne hjk, Fintype.sum_eq_add j k hjk ?_] at h
  · rw [hy.2 j, hz.2 k] at h
    linear_combination h
  · intro c ⟨hcj, hck⟩
    rcases lt_or_gt_of_ne hcj with hc | hc
    · rw [up_zero hy hc, zero_mul]
    · have hc' : (j : ℕ) < c := hc
      have hck' : (c : ℕ) ≠ k := fun h' => hck (Fin.ext h')
      have hkc : k < c := by
        show (k : ℕ) < c
        omega
      rw [up_zero hz hkc, mul_zero]

private lemma isLowUni_mul' {n : ℕ} {x y : Matrix (Fin n) (Fin n) K} (hx : IsLowUni x)
    (hy : IsLowUni y) : IsLowUni (x * y) := by
  have h1 : (x * y).IsLowerTriangular := Matrix.BlockTriangular.mul hx.1 hy.1
  unfold IsLowUni
  refine ⟨h1, fun a => ?_⟩
  rw [Matrix.mul_apply, Finset.sum_eq_single a]
  · rw [hx.2 a, hy.2 a, one_mul]
  · intro b _ hb
    rcases lt_or_gt_of_ne hb with h | h
    · rw [low_zero hy h, mul_zero]
    · rw [low_zero hx h, zero_mul]
  · simp

private lemma isLowUni_inv' {n : ℕ} {x : Matrix (Fin n) (Fin n) K} (hx : IsLowUni x) :
    IsLowUni x⁻¹ := by
  have hd : IsUnit x.det := by
    rw [Matrix.det_of_isLowerTriangular x hx.1]
    simp [hx.2]
  letI := Matrix.invertibleOfIsUnitDet x hd
  have h1 : x⁻¹.IsLowerTriangular := Matrix.blockTriangular_inv_of_blockTriangular hx.1
  unfold IsLowUni
  refine ⟨h1, fun a => ?_⟩
  have h := congrFun (congrFun (mul_inv_one_low hx) a) a
  rw [Matrix.mul_apply, Finset.sum_eq_single a, hx.2 a, one_mul, Matrix.one_apply_eq] at h
  · exact h
  · intro b _ hb
    rcases lt_or_gt_of_ne hb with h' | h'
    · have hz : x⁻¹ b a = 0 := h1 (show OrderDual.toDual a < OrderDual.toDual b from h')
      rw [hz, mul_zero]
    · rw [low_zero hx h', zero_mul]
  · simp

private lemma isUpUni_mul' {n : ℕ} {x y : Matrix (Fin n) (Fin n) K} (hx : IsUpUni x)
    (hy : IsUpUni y) : IsUpUni (x * y) := by
  have h1 : (x * y).IsUpperTriangular := Matrix.BlockTriangular.mul hx.1 hy.1
  unfold IsUpUni
  refine ⟨h1, fun a => ?_⟩
  rw [Matrix.mul_apply, Finset.sum_eq_single a]
  · rw [hx.2 a, hy.2 a, one_mul]
  · intro b _ hb
    rcases lt_or_gt_of_ne hb with h | h
    · rw [up_zero hx h, zero_mul]
    · rw [up_zero hy h, mul_zero]
  · simp

private lemma isUpUni_inv_lower_unipotent_orbits {n : ℕ} {x : Matrix (Fin n) (Fin n) K} (hx : IsUpUni x) :
    IsUpUni x⁻¹ := by
  have hd : IsUnit x.det := by
    rw [Matrix.det_of_isUpperTriangular hx.1]
    simp [hx.2]
  letI := Matrix.invertibleOfIsUnitDet x hd
  have h1 : x⁻¹.IsUpperTriangular := Matrix.blockTriangular_inv_of_blockTriangular hx.1
  unfold IsUpUni
  refine ⟨h1, fun a => ?_⟩
  have h := congrFun (congrFun (mul_inv_one_up hx) a) a
  rw [Matrix.mul_apply, Finset.sum_eq_single a, hx.2 a, one_mul, Matrix.one_apply_eq] at h
  · exact h
  · intro b _ hb
    rcases lt_or_gt_of_ne hb with h' | h'
    · rw [up_zero hx h', zero_mul]
    · have hz : x⁻¹ b a = 0 := h1 (show id a < id b from h')
      rw [hz, mul_zero]
  · simp

private lemma sum_superdiagonal_eq_sum_ite {n : ℕ} (M : Matrix (Fin n) (Fin n) K) :
    (∑ j : Fin n, if h : (j : ℕ) + 1 < n then M j ⟨j + 1, h⟩ else 0) =
      ∑ a : Fin n, ∑ c : Fin n, if (c : ℕ) = a + 1 then M a c else 0 := by
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs with h
  · rw [Finset.sum_eq_single (⟨a + 1, h⟩ : Fin n)]
    · simp
    · intro b _ hb
      rw [if_neg (show ¬ ((b : ℕ) = a + 1) from fun e => hb (Fin.ext e))]
    · simp
  · symm
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [if_neg (show ¬ ((c : ℕ) = a + 1) from fun e => h (by have := c.2; omega))]

private lemma sum_subdiagonal_eq_sum_ite {n : ℕ} (M : Matrix (Fin n) (Fin n) K) :
    (∑ j : Fin n, if h : (j : ℕ) + 1 < n then M ⟨j + 1, h⟩ j else 0) =
      ∑ a : Fin n, ∑ c : Fin n, if (a : ℕ) = c + 1 then M a c else 0 := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs with h
  · rw [Finset.sum_eq_single (⟨c + 1, h⟩ : Fin n)]
    · simp
    · intro b _ hb
      rw [if_neg (show ¬ ((b : ℕ) = c + 1) from fun e => hb (Fin.ext e))]
    · simp
  · symm
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [if_neg (show ¬ ((a : ℕ) = c + 1) from fun e => h (by have := a.2; omega))]

theorem phase_main : PhaseWellDef := by
  unfold PhaseWellDef
  intro K _ s t x y hx hy h
  unfold sLow sUp
  have hyinv : y⁻¹ = ptI s t * x * pt s t := by
    apply Matrix.inv_eq_left_inv
    rw [show ptI s t * x * pt s t * y = ptI s t * (x * pt s t * y) by
      simp only [Matrix.mul_assoc], h, ptI_mul_pt]
  have hzU : IsUpUni y⁻¹ := isUpUni_inv_lower_unipotent_orbits hy
  have hz : ∀ a c, y⁻¹ (revF s a) (revF s c) =
      ↑(t (blk s a))⁻¹ * x a c * ↑(t (blk s c)) := by
    intro a c
    rw [hyinv, conj_apply]
    simp only [revF_revF, blk_revF]
  have hxz : ∀ a c : Fin s.sum, (a : ℕ) = c + 1 → blk s a ≠ blk s c → x a c = 0 := by
    intro a c hac hb
    have hlt : blk s c < blk s a :=
      lt_of_le_of_ne (blk_mono s c a (by omega)) (Ne.symm hb)
    have h0 := hz a c
    rw [up_zero hzU (revF_lt_of_blk_lt s hlt)] at h0
    exact (Units.mul_right_eq_zero _).1 ((Units.mul_left_eq_zero _).1 h0.symm)
  have hterm : ∀ a c : Fin s.sum,
      (if (revF s c : ℕ) = revF s a + 1 then ↑(t (blk s a))⁻¹ * x a c * ↑(t (blk s c)) else 0) =
      (if (a : ℕ) = c + 1 then x a c else 0) := by
    intro a c
    by_cases h1 : (a : ℕ) = c + 1
    · rw [if_pos h1]
      by_cases hb : blk s a = blk s c
      · have hs := revIn_succ s c (by have := a.2; omega) (by rw [← h1]; exact hb.symm)
        rw [← h1] at hs
        rw [if_pos (show (revF s c : ℕ) = revF s a + 1 by rw [revF_val, revF_val]; omega), hb,
          mul_assoc, mul_comm (x a c), ← mul_assoc, Units.inv_mul, one_mul]
      · rw [hxz a c h1 hb]
        simp
    · rw [if_neg h1]
      by_cases h2 : (revF s c : ℕ) = revF s a + 1
      · rw [if_pos h2]
        by_cases hb : blk s a = blk s c
        · exfalso
          have hs := revIn_succ s (revF s a) (by have := (revF s c).2; omega)
            (by rw [← h2, blk_revF, blk_revF, hb])
          rw [← h2] at hs
          have e1 : revIn s (revF s c) = c := congrArg Fin.val (revF_revF s c)
          have e2 : revIn s (revF s a) = a := congrArg Fin.val (revF_revF s a)
          omega
        · have hle : blk s a ≤ blk s c := by
            have := blk_mono s (revF s a) (revF s c) (by omega)
            rwa [blk_revF, blk_revF] at this
          have hlt : blk s a < blk s c := lt_of_le_of_ne hle hb
          have hac : a < c := by
            by_contra hca
            have := blk_mono s c a (not_lt.1 hca)
            omega
          rw [low_zero hx hac, mul_zero, zero_mul]
      · rw [if_neg h2]
  have hy1 := mul_inv_one_up hy
  have hyz : ∀ a c : Fin s.sum, (if (c : ℕ) = a + 1 then y a c else 0) =
      -(if (c : ℕ) = a + 1 then y⁻¹ a c else 0) := by
    intro a c
    split_ifs with hc
    · have := simple_add_zero hy hzU hy1 a c hc
      linear_combination this
    · simp
  rw [sum_subdiagonal_eq_sum_ite x, sum_superdiagonal_eq_sum_ite y]
  have hS : (∑ a : Fin s.sum, ∑ c : Fin s.sum, if (c : ℕ) = a + 1 then y a c else 0) =
      -∑ a : Fin s.sum, ∑ c : Fin s.sum, if (a : ℕ) = c + 1 then x a c else 0 := by
    calc (∑ a : Fin s.sum, ∑ c : Fin s.sum, if (c : ℕ) = a + 1 then y a c else 0)
        = -∑ a : Fin s.sum, ∑ c : Fin s.sum, if (c : ℕ) = a + 1 then y⁻¹ a c else 0 := by
          simp only [hyz, Finset.sum_neg_distrib]
      _ = -∑ a : Fin s.sum, ∑ c : Fin s.sum,
            if (revF s c : ℕ) = revF s a + 1 then y⁻¹ (revF s a) (revF s c) else 0 := by
          congr 1
          refine Fintype.sum_equiv (Function.Involutive.toPerm _ (revF_revF s)) _ _ fun a => ?_
          refine Fintype.sum_equiv (Function.Involutive.toPerm _ (revF_revF s)) _ _ fun c => ?_
          first
          | simp only [Function.Involutive.coe_toPerm, revF_revF]
          | simp [Function.Involutive.toPerm, revF_revF]
      _ = -∑ a : Fin s.sum, ∑ c : Fin s.sum, if (a : ℕ) = c + 1 then x a c else 0 := by
          congr 1
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
          rw [hz a c, hterm a c]
  rw [hS]
  ring

def bdiag (s : List ℕ) (x : Matrix (Fin s.sum) (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K :=
  fun a c => if blk s a = blk s c then x a c else 0

private lemma bdiag_apply (s : List ℕ) (x : Matrix (Fin s.sum) (Fin s.sum) K)
    (a c : Fin s.sum) : bdiag s x a c = if blk s a = blk s c then x a c else 0 := rfl

theorem bdiag_low (s : List ℕ) {x : Matrix (Fin s.sum) (Fin s.sum) K} (hx : IsLowUni x) :
    IsLowUni (bdiag s x) := by
  unfold IsLowUni
  constructor
  · intro i j h
    have h' : i < j := h
    rw [bdiag_apply]
    split_ifs
    · exact low_zero hx h'
    · rfl
  · intro a
    rw [bdiag_apply, if_pos rfl, hx.2 a]

theorem bdiag_inv_blk (s : List ℕ) {x : Matrix (Fin s.sum) (Fin s.sum) K} (hx : IsLowUni x)
    {a c : Fin s.sum} (h : blk s a ≠ blk s c) : (bdiag s x)⁻¹ a c = 0 := by
  have hBinv : bdiag s x * (bdiag s x)⁻¹ = 1 := mul_inv_one_low (bdiag_low s hx)
  have hP : bdiag s x * bdiag s (bdiag s x)⁻¹ = 1 := by
    ext a' c'
    have h1 := congrFun (congrFun hBinv a') c'
    rw [Matrix.mul_apply] at h1
    rw [Matrix.mul_apply]
    by_cases hac : blk s a' = blk s c'
    · rw [← h1]
      refine Finset.sum_congr rfl fun b _ => ?_
      by_cases hab : blk s a' = blk s b
      · rw [bdiag_apply s ((bdiag s x)⁻¹), if_pos (hab.symm.trans hac)]
      · rw [bdiag_apply s x, if_neg hab, zero_mul, zero_mul]
    · rw [Matrix.one_apply_ne (fun h' => hac (by rw [h']))]
      refine Finset.sum_eq_zero fun b _ => ?_
      by_cases hab : blk s a' = blk s b
      · rw [bdiag_apply s ((bdiag s x)⁻¹), if_neg (fun h' => hac (hab.trans h')), mul_zero]
      · rw [bdiag_apply s x, if_neg hab, zero_mul]
  rw [Matrix.inv_eq_right_inv hP, bdiag_apply, if_neg h]

theorem mul_inv_blockDiag_apply_same_block (s : List ℕ) {x : Matrix (Fin s.sum) (Fin s.sum) K} (hx : IsLowUni x)
    {a c : Fin s.sum} (hac : blk s a = blk s c) :
    (x * (bdiag s x)⁻¹) a c = (1 : Matrix (Fin s.sum) (Fin s.sum) K) a c := by
  have hBinv := mul_inv_one_low (bdiag_low s hx)
  rw [← hBinv, Matrix.mul_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases hbc : blk s b = blk s c
  · rw [bdiag_apply s x a b, if_pos (hac.trans hbc.symm)]
  · rw [bdiag_inv_blk s hx hbc, mul_zero, mul_zero]

theorem section_exists (s : List ℕ) (t : ℕ → Kˣ) {x y : Matrix (Fin s.sum) (Fin s.sum) K}
    (hx : IsLowUni x) (hy : IsUpUni y) :
    ∃ v u h : Matrix (Fin s.sum) (Fin s.sum) K, IsLowUni v ∧ IsLowUni h ∧
      v * pt s t = pt s t * h ∧ IsUpUni u ∧ v * pt s t * u = x * pt s t * y := by
  have hv1 : IsLowUni (x * (bdiag s x)⁻¹) := isLowUni_mul' hx (isLowUni_inv' (bdiag_low s hx))
  have hW : IsUpUni (ptI s t * bdiag s x * pt s t) := by
    unfold IsUpUni
    constructor
    · intro a c hca
      have hca' : c < a := hca
      rw [conj_apply]
      have hw : bdiag s x (revF s a) (revF s c) = 0 := by
        rw [bdiag_apply]
        by_cases hb : blk s a = blk s c
        · rw [if_pos (show blk s (revF s a) = blk s (revF s c) by rw [blk_revF, blk_revF, hb]),
            low_zero hx (revF_lt_of_blk_eq s hb.symm hca')]
        · rw [if_neg (show ¬ blk s (revF s a) = blk s (revF s c) by
            rw [blk_revF, blk_revF]; exact hb)]
      rw [hw, mul_zero, zero_mul]
    · intro a
      rw [conj_apply, bdiag_apply, if_pos rfl, hx.2, mul_one, Units.inv_mul]
  refine ⟨x * (bdiag s x)⁻¹, ptI s t * bdiag s x * pt s t * y,
    ptI s t * (x * (bdiag s x)⁻¹) * pt s t, hv1, ?_, ?_, isUpUni_mul' hW hy, ?_⟩
  · unfold IsLowUni
    constructor
    · intro a c hac
      have hac' : a < c := hac
      rw [conj_apply]
      have hv : (x * (bdiag s x)⁻¹) (revF s a) (revF s c) = 0 := by
        by_cases hb : blk s a = blk s c
        · rw [mul_inv_blockDiag_apply_same_block s hx (a := revF s a) (c := revF s c) (by rw [blk_revF, blk_revF, hb]),
            Matrix.one_apply_ne (fun h' => (ne_of_lt hac') (revF_inj s h'))]
        · exact low_zero hv1 (revF_lt_of_blk_lt s (blk_lt_of_lt_of_ne s hac' hb))
      rw [hv, mul_zero, zero_mul]
    · intro a
      rw [conj_apply, mul_inv_blockDiag_apply_same_block s hx (a := revF s a) (c := revF s a) rfl, Matrix.one_apply_eq,
        mul_one, Units.inv_mul]
  · simp only [← Matrix.mul_assoc, pt_mul_ptI, Matrix.one_mul]
  · calc x * (bdiag s x)⁻¹ * pt s t * (ptI s t * bdiag s x * pt s t * y)
        = x * ((bdiag s x)⁻¹ * ((pt s t * ptI s t) * bdiag s x)) * pt s t * y := by
          simp only [Matrix.mul_assoc]
      _ = x * pt s t * y := by
          rw [pt_mul_ptI, Matrix.one_mul, inv_mul_one_low (bdiag_low s hx), Matrix.mul_one]

theorem section_unique (s : List ℕ) (t : ℕ → Kˣ) {v u h v' u' h' : Matrix (Fin s.sum) (Fin s.sum) K}
    (hh : IsLowUni h) (hh' : IsLowUni h') (hu : IsUpUni u) (hu' : IsUpUni u')
    (hvw : v * pt s t = pt s t * h) (hvw' : v' * pt s t = pt s t * h')
    (heq : v' * pt s t * u' = v * pt s t * u) : v' = v ∧ u' = u := by
  have e1 : h' * u' = h * u := by
    have e0 : pt s t * (h' * u') = pt s t * (h * u) := by
      rw [← Matrix.mul_assoc, ← hvw', ← Matrix.mul_assoc, ← hvw, heq]
    calc h' * u' = ptI s t * (pt s t * (h' * u')) := by
          rw [← Matrix.mul_assoc, ptI_mul_pt, Matrix.one_mul]
      _ = ptI s t * (pt s t * (h * u)) := by rw [e0]
      _ = h * u := by rw [← Matrix.mul_assoc, ptI_mul_pt, Matrix.one_mul]
  have e2 : h⁻¹ * h' = u * u'⁻¹ := by
    calc h⁻¹ * h' = h⁻¹ * h' * (u' * u'⁻¹) := by rw [mul_inv_one_up hu', Matrix.mul_one]
      _ = h⁻¹ * (h' * u') * u'⁻¹ := by simp only [Matrix.mul_assoc]
      _ = h⁻¹ * (h * u) * u'⁻¹ := by rw [e1]
      _ = u * u'⁻¹ := by rw [← Matrix.mul_assoc h⁻¹ h, inv_mul_one_low hh, Matrix.one_mul]
  have hl : IsLowUni (h⁻¹ * h') := isLowUni_mul K (isLowUni_inv K hh) hh'
  have hup : IsUpUni (u * u'⁻¹) := isUpUni_mul K hu (isUpUni_inv K hu')
  have e3 : h⁻¹ * h' = 1 := eq_one_of_low_up hl (e2 ▸ hup)
  have e4 : u * u'⁻¹ = 1 := e2 ▸ e3
  have hheq : h' = h := by
    calc h' = h * (h⁻¹ * h') := by rw [← Matrix.mul_assoc, mul_inv_one_low hh, Matrix.one_mul]
      _ = h := by rw [e3, Matrix.mul_one]
  have hueq : u' = u := by
    calc u' = u * u'⁻¹ * u' := by rw [e4, Matrix.one_mul]
      _ = u := by rw [Matrix.mul_assoc, inv_mul_one_up hu', Matrix.mul_one]
  refine ⟨?_, hueq⟩
  calc v' = v' * pt s t * ptI s t := by rw [Matrix.mul_assoc, pt_mul_ptI, Matrix.mul_one]
    _ = pt s t * h' * ptI s t := by rw [hvw']
    _ = v * pt s t * ptI s t := by rw [hheq, hvw]
    _ = v := by rw [Matrix.mul_assoc, pt_mul_ptI, Matrix.mul_one]

theorem section_main : SectionBij := by
  unfold SectionBij
  intro K _ s t x y hx hy
  obtain ⟨v, u, h, hv, hh, hvw, hu, heq⟩ := section_exists s t hx hy
  refine ⟨(v, u), ⟨⟨hv, h, hh, hvw⟩, hu, heq⟩, ?_⟩
  rintro ⟨v', u'⟩ ⟨⟨hv', h', hh', hvw'⟩, hu', heq'⟩
  obtain ⟨e1, e2⟩ := section_unique s t hh hh' hu hu' hvw hvw' (heq'.trans heq.symm)
  simp only [Prod.mk.injEq]
  exact ⟨e1, e2⟩

end Phase

theorem phaseWellDef : Formalism.DoubleCosetMeasures.PhaseWellDef := Phase.phase_main

theorem sectionBij : Formalism.DoubleCosetMeasures.SectionBij := Phase.section_main

end Formalism.DoubleCosetMeasures.P
