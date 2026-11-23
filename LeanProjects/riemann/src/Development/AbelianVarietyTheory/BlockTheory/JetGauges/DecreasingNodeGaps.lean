import Mathlib

namespace GlobalTheory.IndefiniteRowSideFullHecke.DecreasingNodeGaps

theorem card_eq (r k : ℕ) (hk : 1 ≤ k) : 2 * r + k + 1 = (k - 1) + (2 * r + 2) := by omega

def param (r k : ℕ) (hk : 1 ≤ k) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ) :
    Fin (2 * r + k + 1) → ℝ :=
  fun s => Fin.append v (fun i => -b i) (Fin.cast (card_eq r k hk) s)

def cloudIdx (r k : ℕ) (j : Fin (k - 1)) : Fin (2 * r + k + 1) := ⟨j.val, by omega⟩

def nodeIdx (r k : ℕ) (hk : 1 ≤ k) (i : Fin (2 * r + 2)) : Fin (2 * r + k + 1) :=
  ⟨k - 1 + i.val, by omega⟩

def IsDecreasing (r k : ℕ) (hk : 1 ≤ k) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ) : Prop :=
  StrictAnti (param r k hk v b)

def sign (r k : ℕ) (hk : 1 ≤ k) : Fin (2 * r + k + 1) → Bool :=
  fun s => Fin.append (fun _ : Fin (k - 1) => true)
    (fun i : Fin (2 * r + 2) => decide (Even i.val)) (Fin.cast (card_eq r k hk) s)

def Interlaces (r k : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (u : Fin k → ℝ) : Prop :=
  (∀ i : Fin k, lam ⟨i.val, by omega⟩ < u i) ∧
    ∀ (i : ℕ) (hi : i + 1 < k), u ⟨i + 1, hi⟩ < lam ⟨i, by omega⟩

def Parity (r k : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (u : Fin k → ℝ) : Prop :=
  ∀ (s : Fin (2 * r + k + 1)) (i : Fin k), ∃ z : ℤ, lam s - u i = (z : ℝ) + 1 / 2

def IsShiftedIntegral {d : ℕ} (x : Fin d → ℝ) : Prop :=
  ∀ s : Fin d, ∃ z : ℤ, x s = (z : ℝ) + ((d : ℝ) - 1) / 2

def NodeGapGe (r : ℕ) (b : Fin (2 * r + 2) → ℝ) (h : ℝ) : Prop :=
  ∀ (i : ℕ) (hi : i + 1 < 2 * r + 2), h ≤ (-b ⟨i, by omega⟩) - (-b ⟨i + 1, hi⟩)

def NoncompactGapGe (r k : ℕ) (hk : 1 ≤ k) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ) : Prop :=
  ∀ s t : Fin (2 * r + k + 1), sign r k hk s ≠ sign r k hk t → h ≤ |lam s - lam t|

@[simp] theorem param_cloud (r k : ℕ) (hk : 1 ≤ k) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ) (j : Fin (k - 1)) : param r k hk v b (cloudIdx r k j) = v j := by
  have : Fin.cast (card_eq r k hk) (cloudIdx r k j) = Fin.castAdd (2 * r + 2) j := rfl
  simp only [param, this, Fin.append_left]

@[simp] theorem param_node (r k : ℕ) (hk : 1 ≤ k) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ) (i : Fin (2 * r + 2)) :
    param r k hk v b (nodeIdx r k hk i) = -b i := by
  have : Fin.cast (card_eq r k hk) (nodeIdx r k hk i) = Fin.natAdd (k - 1) i := rfl
  simp only [param, this, Fin.append_right]

@[simp] theorem sign_cloud (r k : ℕ) (hk : 1 ≤ k) (j : Fin (k - 1)) :
    sign r k hk (cloudIdx r k j) = true := by
  have : Fin.cast (card_eq r k hk) (cloudIdx r k j) = Fin.castAdd (2 * r + 2) j := rfl
  simp only [sign, this, Fin.append_left]

@[simp] theorem sign_node (r k : ℕ) (hk : 1 ≤ k) (i : Fin (2 * r + 2)) :
    sign r k hk (nodeIdx r k hk i) = decide (Even i.val) := by
  have : Fin.cast (card_eq r k hk) (nodeIdx r k hk i) = Fin.natAdd (k - 1) i := rfl
  simp only [sign, this, Fin.append_right]

theorem parity_of_isShiftedIntegral (r k : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (u : Fin k → ℝ)
    (hl : IsShiftedIntegral lam) (hu : IsShiftedIntegral u) : Parity r k lam u := by
  intro s i
  obtain ⟨a, ha⟩ := hl s
  obtain ⟨c, hc⟩ := hu i
  refine ⟨a - c + r, ?_⟩
  rw [ha, hc]
  push_cast
  ring

theorem nodeGapGe_of_noncompactGapGe (r k : ℕ) (hk : 1 ≤ k) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ) (h : ℝ) (hd : IsDecreasing r k hk v b)
    (hg : NoncompactGapGe r k hk (param r k hk v b) h) : NodeGapGe r b h := by
  intro i hi
  have hlt : nodeIdx r k hk ⟨i, by omega⟩ < nodeIdx r k hk ⟨i + 1, hi⟩ := by
    simp [nodeIdx, Fin.lt_def]
  have h1 := hd hlt
  have h2 := hg (nodeIdx r k hk ⟨i, by omega⟩) (nodeIdx r k hk ⟨i + 1, hi⟩) (by
    simp only [sign_node, Nat.even_add_one]
    by_cases he : Even i <;> simp [he])
  simp only [param_node] at h1 h2
  rwa [abs_of_pos (by linarith)] at h2

example : List.ofFn (sign 1 2 (by norm_num)) = [true, true, false, true, false] := by decide

example :
    IsDecreasing 0 2 (by norm_num) ![1] ![8, 10] ∧
    Interlaces 0 2 (param 0 2 (by norm_num) ![1] ![8, 10]) ![5 / 2, -1 / 2] ∧
    Parity 0 2 (param 0 2 (by norm_num) ![1] ![8, 10]) ![5 / 2, -1 / 2] ∧
    NodeGapGe 0 ![8, 10] 2 := by
  have hp : param 0 2 (by norm_num) ![1] ![8, 10] = ![1, -8, -10] := by
    funext s
    fin_cases s <;> rfl
  refine ⟨?_, ⟨?_, ?_⟩, ?_, ?_⟩
  · unfold IsDecreasing
    rw [hp]
    intro s t hst
    fin_cases s <;> fin_cases t <;> simp_all <;> norm_num
  · rw [hp]
    intro i
    fin_cases i <;> simp <;> norm_num
  · rw [hp]
    intro i hi
    obtain rfl : i = 0 := by omega
    simp
    norm_num
  · apply parity_of_isShiftedIntegral
    · rw [hp]
      intro s
      fin_cases s
      · exact ⟨0, by simp; norm_num⟩
      · exact ⟨-9, by simp; norm_num⟩
      · exact ⟨-11, by simp; norm_num⟩
    · intro s
      fin_cases s
      · exact ⟨2, by simp; norm_num⟩
      · exact ⟨-1, by simp; norm_num⟩
  · intro i hi
    obtain rfl : i = 0 := by omega
    simp
    norm_num

end GlobalTheory.IndefiniteRowSideFullHecke.DecreasingNodeGaps
