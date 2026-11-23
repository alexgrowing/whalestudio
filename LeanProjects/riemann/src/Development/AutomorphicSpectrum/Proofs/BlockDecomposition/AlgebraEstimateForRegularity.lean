import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt

noncomputable section

open Finset
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.SkewWords

variable {V ι : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [Fintype ι]
  (X : ι → Module.End ℂ V)

def wd (w : List ι) : Module.End ℂ V := (w.map X).prod

def lap : Module.End ℂ V := -∑ i, X i * X i

def bsum (m : ℕ) (u : V) : ℝ := ∑ v : List.Vector ι m, ‖wd X v.1 u‖

def qsum (m : ℕ) (u : V) : ℝ := ∑ j ∈ range (m + 1), ‖(lap X ^ j) u‖

def wspan (m : ℕ) : Submodule ℂ (Module.End ℂ V) :=
  Submodule.span ℂ {T | ∃ w : List ι, w.length = m ∧ T = wd X w}

theorem wd_nil : wd X [] = 1 := by simp [wd]

theorem wd_cons (a : ι) (w : List ι) : wd X (a :: w) = X a * wd X w := by simp [wd]

theorem wd_concat (a : ι) (w : List ι) : wd X (w ++ [a]) = wd X w * X a := by simp [wd]

theorem norm_le_bsum {m : ℕ} (w : List ι) (hw : w.length = m) (u : V) : ‖wd X w u‖ ≤ bsum X m u :=
  let v : List.Vector ι m := ⟨w, hw⟩
  Finset.single_le_sum (s := (univ : Finset (List.Vector ι m))) (f := fun v : List.Vector ι m => ‖wd X v.1 u‖)
    (fun _ _ => norm_nonneg _) (mem_univ v)

theorem bsum_nonneg (m : ℕ) (u : V) : 0 ≤ bsum X m u := sum_nonneg fun _ _ => norm_nonneg _

theorem qsum_nonneg (m : ℕ) (u : V) : 0 ≤ qsum X m u := sum_nonneg fun _ _ => norm_nonneg _

theorem qsum_le_succ (m : ℕ) (u : V) : qsum X m u ≤ qsum X (m + 1) u := by
  unfold qsum
  rw [sum_range_succ _ (m + 1)]
  exact le_add_of_nonneg_right (norm_nonneg _)

theorem qsum_lap_le (m : ℕ) (u : V) : qsum X m (lap X u) ≤ qsum X (m + 1) u := by
  unfold qsum
  rw [sum_range_succ' _ (m + 1)]
  have : ∀ j, ‖(lap X ^ j) (lap X u)‖ = ‖(lap X ^ (j + 1)) u‖ := fun j => by
    rw [pow_succ, Module.End.mul_apply]
  simp only [this]
  exact le_add_of_nonneg_right (norm_nonneg _)

theorem bound_of_mem {m : ℕ} {T : Module.End ℂ V} (hT : T ∈ wspan X m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u, ‖T u‖ ≤ C * bsum X m u := by
  induction hT using Submodule.span_induction with
  | mem T h =>
    obtain ⟨w, hw, rfl⟩ := h
    exact ⟨1, zero_le_one, fun u => by simpa using norm_le_bsum X w hw u⟩
  | zero => exact ⟨0, le_rfl, fun u => by simp⟩
  | add S T _ _ hS hT =>
    obtain ⟨C, hC, h⟩ := hS
    obtain ⟨D, hD, k⟩ := hT
    refine ⟨C + D, add_nonneg hC hD, fun u => ?_⟩
    calc ‖(S + T) u‖ ≤ ‖S u‖ + ‖T u‖ := norm_add_le _ _
      _ ≤ C * bsum X m u + D * bsum X m u := add_le_add (h u) (k u)
      _ = _ := by ring
  | smul a T _ hT =>
    obtain ⟨C, hC, h⟩ := hT
    refine ⟨‖a‖ * C, by positivity, fun u => ?_⟩
    rw [LinearMap.smul_apply, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h u) (norm_nonneg _)

theorem mul_left_mem {m : ℕ} {T : Module.End ℂ V} (a : ι) (hT : T ∈ wspan X m) :
    X a * T ∈ wspan X (m + 1) := by
  induction hT using Submodule.span_induction with
  | mem T h =>
    obtain ⟨w, hw, rfl⟩ := h
    exact Submodule.subset_span ⟨a :: w, by simp [hw], (wd_cons X a w).symm⟩
  | zero => simp
  | add S T _ _ hS hT => rw [mul_add]; exact add_mem hS hT
  | smul c T _ hT => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hT

theorem mul_right_mem {m : ℕ} {T : Module.End ℂ V} (a : ι) (hT : T ∈ wspan X m) :
    T * X a ∈ wspan X (m + 1) := by
  induction hT using Submodule.span_induction with
  | mem T h =>
    obtain ⟨w, hw, rfl⟩ := h
    exact Submodule.subset_span ⟨w ++ [a], by simp [hw], (wd_concat X a w).symm⟩
  | zero => simp
  | add S T _ _ hS hT => rw [add_mul]; exact add_mem hS hT
  | smul c T _ hT => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ hT

theorem comm_mem (c : ι → ι → ι → ℝ) (hc : ∀ i j, X i * X j - X j * X i = ∑ k, (c i j k : ℂ) • X k)
    (i : ι) (w : List ι) : X i * wd X w - wd X w * X i ∈ wspan X w.length := by
  induction w with
  | nil => simp [wd_nil]
  | cons a w ih =>
    have e : X i * wd X (a :: w) - wd X (a :: w) * X i =
        (X i * X a - X a * X i) * wd X w + X a * (X i * wd X w - wd X w * X i) := by
      rw [wd_cons]; noncomm_ring
    rw [e, hc, Finset.sum_mul]
    refine add_mem (sum_mem fun k _ => ?_) (mul_left_mem X a ih)
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k :: w, by simp, (wd_cons X k w).symm⟩)

theorem lap_comm_mem (c : ι → ι → ι → ℝ) (hc : ∀ i j, X i * X j - X j * X i = ∑ k, (c i j k : ℂ) • X k)
    (w : List ι) : lap X * wd X w - wd X w * lap X ∈ wspan X (w.length + 1) := by
  have h : ∀ i, X i * (X i * wd X w - wd X w * X i) + (X i * wd X w - wd X w * X i) * X i =
      X i * X i * wd X w - wd X w * (X i * X i) := fun i => by noncomm_ring
  have e : lap X * wd X w - wd X w * lap X =
      -∑ i, (X i * (X i * wd X w - wd X w * X i) + (X i * wd X w - wd X w * X i) * X i) := by
    simp only [h, sum_sub_distrib, lap, neg_mul, mul_neg, Finset.sum_mul, Finset.mul_sum]
    abel
  rw [e]
  exact neg_mem (sum_mem fun i _ => add_mem (mul_left_mem X i (comm_mem X c hc i w))
    (mul_right_mem X i (comm_mem X c hc i w)))

theorem lap_comm_bound (c : ι → ι → ι → ℝ)
    (hc : ∀ i j, X i * X j - X j * X i = ∑ k, (c i j k : ℂ) • X k) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : List ι, w.length = m → ∀ u,
      ‖(lap X * wd X w - wd X w * lap X) u‖ ≤ C * bsum X (m + 1) u := by
  have h : ∀ v : List.Vector ι m, ∃ C : ℝ, 0 ≤ C ∧ ∀ u,
      ‖(lap X * wd X v.1 - wd X v.1 * lap X) u‖ ≤ C * bsum X (m + 1) u := fun v => by
    have := lap_comm_mem X c hc v.1
    rw [v.2] at this
    exact bound_of_mem X this
  choose C hC h using h
  refine ⟨∑ v, C v, sum_nonneg fun v _ => hC v, fun w hw u => ?_⟩
  refine (h ⟨w, hw⟩ u).trans (mul_le_mul_of_nonneg_right ?_ (bsum_nonneg X _ u))
  exact Finset.single_le_sum (f := C) (fun v _ => hC v) (mem_univ _)

theorem sum_sq_eq (hs : ∀ i u v, ⟪X i u, v⟫_ℂ = -⟪u, X i v⟫_ℂ) (a : V) :
    ∑ i, ‖X i a‖ ^ 2 = (⟪a, lap X a⟫_ℂ).re := by
  have h : lap X a = -∑ i, X i (X i a) := by
    simp [lap, Module.End.mul_apply, LinearMap.sum_apply]
  rw [h, inner_neg_right, inner_sum, Complex.neg_re, Complex.re_sum, ← Finset.sum_neg_distrib]
  refine sum_congr rfl fun i _ => ?_
  have e : ⟪a, X i (X i a)⟫_ℂ = -⟪X i a, X i a⟫_ℂ := by rw [hs]; simp
  rw [e, Complex.neg_re, neg_neg]
  simpa using (inner_self_eq_norm_sq (𝕜 := ℂ) (X i a)).symm

theorem sq_le_lap (hs : ∀ i u v, ⟪X i u, v⟫_ℂ = -⟪u, X i v⟫_ℂ) (i : ι) (a : V) :
    ‖X i a‖ ^ 2 ≤ (⟪a, lap X a⟫_ℂ).re := by
  rw [← sum_sq_eq X hs]
  exact Finset.single_le_sum (f := fun i => ‖X i a‖ ^ 2) (fun _ _ => by positivity) (mem_univ i)

theorem core (hs : ∀ i u v, ⟪X i u, v⟫_ℂ = -⟪u, X i v⟫_ℂ) (i b : ι) (w : List ι) (u : V) :
    ‖wd X (i :: b :: w) u‖ ^ 2 ≤ ‖wd X (b :: b :: w) u‖ * ‖wd X w (lap X u)‖ +
      ‖wd X (b :: w) u‖ * ‖(lap X * wd X (b :: w) - wd X (b :: w) * lap X) u‖ := by
  set a := wd X (b :: w) u with ha
  set G := lap X * wd X (b :: w) - wd X (b :: w) * lap X with hG
  have e1 : wd X (i :: b :: w) u = X i a := by rw [wd_cons]; rfl
  have e2 : wd X (b :: b :: w) u = X b a := by rw [wd_cons]; rfl
  have e3 : lap X a = X b (wd X w (lap X u)) + G u := by
    simp only [hG, ha, LinearMap.sub_apply, Module.End.mul_apply, wd_cons]
    abel
  rw [e1, e2]
  refine (sq_le_lap X hs i a).trans ?_
  rw [e3, inner_add_right, Complex.add_re]
  have e4 : ⟪a, X b (wd X w (lap X u))⟫_ℂ = -⟪X b a, wd X w (lap X u)⟫_ℂ := by rw [hs]; simp
  refine add_le_add ?_ ((Complex.re_le_norm _).trans (norm_inner_le_norm _ _))
  rw [e4, Complex.neg_re]
  exact (neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _))

theorem bsum_le_of_sq (m : ℕ) (u : V) (D : ℝ) (hD : 0 ≤ D)
    (h : ∀ v : List.Vector ι m, ‖wd X v.1 u‖ ^ 2 ≤ bsum X m u * D) :
    bsum X m u ≤ (Fintype.card (List.Vector ι m) : ℝ) ^ 2 * D := by
  set b := bsum X m u with hb
  set N : ℝ := ((Fintype.card (List.Vector ι m) : ℕ) : ℝ) with hN
  have hb0 : 0 ≤ b := bsum_nonneg X m u
  have h1 : b ^ 2 ≤ N * ∑ v : List.Vector ι m, ‖wd X v.1 u‖ ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (List.Vector ι m)))
      (f := fun v => ‖wd X v.1 u‖)
    simpa [hb, bsum, hN] using this
  have h2 : ∑ v : List.Vector ι m, ‖wd X v.1 u‖ ^ 2 ≤ N * (b * D) := by
    have := Finset.sum_le_card_nsmul (univ : Finset (List.Vector ι m)) (fun v => ‖wd X v.1 u‖ ^ 2)
      (b * D) (fun v _ => h v)
    simpa [hN] using this
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  have h3 : b ^ 2 ≤ N ^ 2 * D * b := by
    calc b ^ 2 ≤ N * (N * (b * D)) := h1.trans (mul_le_mul_of_nonneg_left h2 hN0)
      _ = _ := by ring
  rcases hb0.eq_or_lt with h0 | h0
  · rw [← h0]; positivity
  · exact le_of_mul_le_mul_right (by nlinarith) h0

theorem bsum_le_card (m : ℕ) (u : V) (D : ℝ) (h : ∀ v : List.Vector ι m, ‖wd X v.1 u‖ ≤ D) :
    bsum X m u ≤ (Fintype.card (List.Vector ι m) : ℝ) * D := by
  have := Finset.sum_le_card_nsmul (univ : Finset (List.Vector ι m)) (fun v => ‖wd X v.1 u‖)
      D (fun v _ => h v)
  simpa [bsum] using this

theorem bound_zero : ∃ C : ℝ, 0 ≤ C ∧ ∀ u, bsum X 0 u ≤ C * qsum X 0 u := by
  refine ⟨_, Nat.cast_nonneg (Fintype.card (List.Vector ι 0)), fun u => bsum_le_card X 0 u _ fun v => ?_⟩
  obtain ⟨w, hw⟩ := v
  obtain rfl : w = [] := List.length_eq_zero_iff.mp hw
  simp [wd_nil, qsum]

theorem bound_one (hs : ∀ i u v, ⟪X i u, v⟫_ℂ = -⟪u, X i v⟫_ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u, bsum X 1 u ≤ C * qsum X 1 u := by
  refine ⟨_, Nat.cast_nonneg (Fintype.card (List.Vector ι 1)), fun u => bsum_le_card X 1 u _ fun v => ?_⟩
  obtain ⟨w, hw⟩ := v
  obtain ⟨i, rfl⟩ := List.length_eq_one_iff.mp hw
  have e : wd X [i] u = X i u := by simp [wd]
  have q : qsum X 1 u = ‖u‖ + ‖lap X u‖ := by simp [qsum, sum_range_succ]
  show ‖wd X [i] u‖ ≤ _
  rw [e, q]
  have h1 : ‖X i u‖ ^ 2 ≤ ‖u‖ * ‖lap X u‖ :=
    (sq_le_lap X hs i u).trans ((Complex.re_le_norm _).trans (norm_inner_le_norm _ _))
  have h2 : 0 ≤ ‖u‖ := norm_nonneg _
  have h3 : 0 ≤ ‖lap X u‖ := norm_nonneg _
  exact abs_le_of_sq_le_sq' (by nlinarith) (by positivity) |>.2

theorem bound_step (hs : ∀ i u v, ⟪X i u, v⟫_ℂ = -⟪u, X i v⟫_ℂ) (c : ι → ι → ι → ℝ)
    (hc : ∀ i j, X i * X j - X j * X i = ∑ k, (c i j k : ℂ) • X k) (m : ℕ)
    (h0 : ∃ C : ℝ, 0 ≤ C ∧ ∀ u, bsum X m u ≤ C * qsum X m u)
    (h1 : ∃ C : ℝ, 0 ≤ C ∧ ∀ u, bsum X (m + 1) u ≤ C * qsum X (m + 1) u) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u, bsum X (m + 2) u ≤ C * qsum X (m + 2) u := by
  obtain ⟨C₁, hC₁, k₁⟩ := h0
  obtain ⟨C₂, hC₂, k₂⟩ := h1
  obtain ⟨C₃, hC₃, k₃⟩ := lap_comm_bound X c hc (m + 1)
  set N : ℝ := ((Fintype.card (List.Vector ι (m + 2)) : ℕ) : ℝ) with hN
  refine ⟨N ^ 2 * (C₁ + C₃ * C₂), by positivity, fun u => ?_⟩
  set b := bsum X (m + 2) u with hb
  have hb0 : 0 ≤ b := bsum_nonneg X _ u
  set D := bsum X m (lap X u) + C₃ * bsum X (m + 1) u with hD
  have hD0 : 0 ≤ D := add_nonneg (bsum_nonneg X _ _) (mul_nonneg hC₃ (bsum_nonneg X _ _))
  have key : ∀ v : List.Vector ι (m + 2), ‖wd X v.1 u‖ ^ 2 ≤ b * D := by
    rintro ⟨w₀, hw₀⟩
    rcases w₀ with _ | ⟨i, _ | ⟨a, w⟩⟩
    · simp at hw₀
    · simp at hw₀
    have hw : w.length = m := by simpa using hw₀
    have t1 : ‖wd X (a :: a :: w) u‖ ≤ b := norm_le_bsum X _ (by simp [hw]) u
    have t2 : ‖wd X w (lap X u)‖ ≤ bsum X m (lap X u) := norm_le_bsum X _ hw _
    have t3 : ‖wd X (a :: w) u‖ ≤ bsum X (m + 1) u := norm_le_bsum X _ (by simp [hw]) u
    have t4 := k₃ (a :: w) (by simp [hw]) u
    have s1 := mul_le_mul t1 t2 (norm_nonneg _) hb0
    have s2 := mul_le_mul t3 t4 (norm_nonneg _) (bsum_nonneg X _ u)
    refine (core X hs i a w u).trans ((add_le_add s1 s2).trans (le_of_eq ?_))
    rw [hD]; ring
  have hbD : b ≤ N ^ 2 * D := bsum_le_of_sq X (m + 2) u D hD0 key
  have q1 : qsum X m (lap X u) ≤ qsum X (m + 2) u :=
    (qsum_lap_le X m u).trans (qsum_le_succ X _ u)
  have q2 : qsum X (m + 1) u ≤ qsum X (m + 2) u := qsum_le_succ X _ u
  have d1 : bsum X m (lap X u) ≤ C₁ * qsum X (m + 2) u :=
    (k₁ _).trans (mul_le_mul_of_nonneg_left q1 hC₁)
  have d2 : C₃ * bsum X (m + 1) u ≤ C₃ * (C₂ * qsum X (m + 2) u) :=
    mul_le_mul_of_nonneg_left ((k₂ _).trans (mul_le_mul_of_nonneg_left q2 hC₂)) hC₃
  have hDle : D ≤ (C₁ + C₃ * C₂) * qsum X (m + 2) u := by
    rw [hD]; nlinarith
  calc b ≤ N ^ 2 * D := hbD
    _ ≤ N ^ 2 * ((C₁ + C₃ * C₂) * qsum X (m + 2) u) := mul_le_mul_of_nonneg_left hDle (by positivity)
    _ = _ := by ring

theorem bound_all (hs : ∀ i u v, ⟪X i u, v⟫_ℂ = -⟪u, X i v⟫_ℂ) (c : ι → ι → ι → ℝ)
    (hc : ∀ i j, X i * X j - X j * X i = ∑ k, (c i j k : ℂ) • X k) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u, bsum X m u ≤ C * qsum X m u := by
  have : (∃ C : ℝ, 0 ≤ C ∧ ∀ u, bsum X m u ≤ C * qsum X m u) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ u, bsum X (m + 1) u ≤ C * qsum X (m + 1) u := by
    induction m with
    | zero => exact ⟨bound_zero X, bound_one X hs⟩
    | succ m ih => exact ⟨ih.2, bound_step X hs c hc m ih.1 ih.2⟩
  exact this.1

theorem algEst : PositivityTheory.RgBcC.AlgEst := by
  intro V ι _ _ _ X c hs hc w
  obtain ⟨C, hC, h⟩ := bound_all X hs c hc w.length
  refine ⟨C, fun u => (norm_le_bsum X w rfl u).trans ((h u).trans (le_of_eq ?_))⟩
  rfl

end GlobalTheory.CompanionTheory.SkewWords
