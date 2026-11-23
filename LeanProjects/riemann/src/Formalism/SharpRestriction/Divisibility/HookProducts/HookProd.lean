import Formalism.LocalToGlobal.Divisibility.Numbers

namespace Formalism.MainNotions.DIV.HookProducts

namespace HookLengthProduct

open Finset

def K (n : ℕ) (a : ℕ → ℕ) (c : ℕ) : ℕ := ((range n).filter (fun l => c < a l)).card

def E (n : ℕ) (a : ℕ → ℕ) : ℕ :=
  ∏ i ∈ range n, ∏ c ∈ range (a i), ((a i - c) + (K n a c - i) - 1)

def D (n : ℕ) (a : ℕ → ℕ) : ℕ :=
  ∏ i ∈ range n, ∏ l ∈ Ioo i n, (a i + l - a l - i)

def F (n : ℕ) (a : ℕ → ℕ) : ℕ := ∏ i ∈ range n, (a i + n - 1 - i).factorial

theorem K_succ_of_zero (m : ℕ) (a : ℕ → ℕ) (h : a m = 0) (c : ℕ) : K (m + 1) a c = K m a c := by
  simp [K, Finset.range_add_one, Finset.filter_insert, h]

theorem K_zero (n : ℕ) (a : ℕ → ℕ) (h1 : ∀ i < n, 1 ≤ a i) : K n a 0 = n := by
  unfold K
  rw [Finset.filter_true_of_mem, Finset.card_range]
  intro l hl
  have := h1 l (Finset.mem_range.mp hl)
  omega

theorem K_shift (n : ℕ) (a : ℕ → ℕ) (h1 : ∀ i < n, 1 ≤ a i) (c : ℕ) :
    K n a (c + 1) = K n (fun i => a i - 1) c := by
  unfold K
  congr 1
  apply Finset.filter_congr
  intro l hl
  have := h1 l (Finset.mem_range.mp hl)
  show c + 1 < a l ↔ c < a l - 1
  omega

theorem prod_range_pos (m : ℕ) (hm : 1 ≤ m) (f : ℕ → ℕ) :
    ∏ c ∈ range m, f c = f 0 * ∏ c ∈ range (m - 1), f (c + 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [Finset.prod_range_succ', mul_comm, Nat.add_sub_cancel]

theorem E_succ_zero (m : ℕ) (a : ℕ → ℕ) (h : a m = 0) : E (m + 1) a = E m a := by
  unfold E
  rw [Finset.prod_range_succ, h, Finset.range_zero, Finset.prod_empty, mul_one]
  refine Finset.prod_congr rfl (fun i _ => Finset.prod_congr rfl (fun c _ => ?_))
  rw [K_succ_of_zero m a h c]

theorem D_succ (m : ℕ) (a : ℕ → ℕ) :
    D (m + 1) a = (∏ i ∈ range m, (a i + m - a m - i)) * D m a := by
  unfold D
  rw [Finset.prod_range_succ]
  have h0 : Ioo m (m + 1) = ∅ := by
    ext x
    simp only [Finset.mem_Ioo]
    simp
    try omega
  rw [h0, Finset.prod_empty, mul_one, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun i hi => ?_)
  have hi' : i < m := Finset.mem_range.mp hi
  have h1 : Ioo i (m + 1) = insert m (Ioo i m) := by
    ext x
    simp only [Finset.mem_Ioo, Finset.mem_insert]
    omega
  rw [h1, Finset.prod_insert (by simp)]

theorem F_succ_zero (m : ℕ) (a : ℕ → ℕ) (h : a m = 0) :
    F (m + 1) a = (∏ i ∈ range m, (a i + m - a m - i)) * F m a := by
  unfold F
  rw [Finset.prod_range_succ, ← Finset.prod_mul_distrib]
  have hl : a m + (m + 1) - 1 - m = 0 := by omega
  rw [hl, Nat.factorial_zero, mul_one]
  refine Finset.prod_congr rfl (fun i hi => ?_)
  have hi' : i < m := Finset.mem_range.mp hi
  have e1 : a i + (m + 1) - 1 - i = (a i + m - 1 - i) + 1 := by omega
  have e2 : a i + m - a m - i = (a i + m - 1 - i) + 1 := by omega
  rw [e1, e2, Nat.factorial_succ]

theorem E_shift (n : ℕ) (a : ℕ → ℕ) (h1 : ∀ i < n, 1 ≤ a i) :
    E n a = (∏ i ∈ range n, (a i + n - 1 - i)) * E n (fun i => a i - 1) := by
  simp only [E]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun i hi => ?_)
  have hi' : i < n := Finset.mem_range.mp hi
  have hai := h1 i hi'
  rw [prod_range_pos (a i) hai]
  congr 1
  · rw [K_zero n a h1]
    omega
  · refine Finset.prod_congr rfl (fun c _ => ?_)
    rw [K_shift n a h1 c]
    omega

theorem D_shift (n : ℕ) (a : ℕ → ℕ) (h1 : ∀ i < n, 1 ≤ a i) :
    D n a = D n (fun i => a i - 1) := by
  simp only [D]
  refine Finset.prod_congr rfl (fun i hi => Finset.prod_congr rfl (fun l hl => ?_))
  have hi' : i < n := Finset.mem_range.mp hi
  have hl' : l < n := (Finset.mem_Ioo.mp hl).2
  have := h1 i hi'
  have := h1 l hl'
  omega

theorem F_shift (n : ℕ) (a : ℕ → ℕ) (h1 : ∀ i < n, 1 ≤ a i) :
    F n a = (∏ i ∈ range n, (a i + n - 1 - i)) * F n (fun i => a i - 1) := by
  simp only [F]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun i hi => ?_)
  have hi' : i < n := Finset.mem_range.mp hi
  have := h1 i hi'
  have e : a i + n - 1 - i = (a i - 1 + n - 1 - i) + 1 := by omega
  rw [e, Nat.factorial_succ]

theorem E_mul_D (n : ℕ) :
    ∀ a : ℕ → ℕ, (∀ i l, i < l → l < n → a l ≤ a i) → E n a * D n a = F n a := by
  induction n with
  | zero => intro a _; simp [E, D, F]
  | succ m ih =>
    suffices H : ∀ k (a : ℕ → ℕ), a m = k → (∀ i l, i < l → l < m + 1 → a l ≤ a i) →
        E (m + 1) a * D (m + 1) a = F (m + 1) a from fun a h => H _ a rfl h
    intro k
    induction k with
    | zero =>
      intro a ha hmono
      rw [E_succ_zero m a ha, D_succ, F_succ_zero m a ha,
        ← ih a (fun i l hil hl => hmono i l hil (by omega))]
      ring
    | succ k ihk =>
      intro a ha hmono
      have h1 : ∀ i < m + 1, 1 ≤ a i := by
        intro i hi
        rcases Nat.lt_or_ge i m with h | h
        · have := hmono i m h (by omega)
          omega
        · have e : i = m := by omega
          rw [e, ha]
          omega
      rw [E_shift (m + 1) a h1, D_shift (m + 1) a h1, F_shift (m + 1) a h1,
        ← ihk (fun i => a i - 1) (by show a m - 1 = k; omega)
          (fun i l hil hl => by
            have := hmono i l hil hl
            show a l - 1 ≤ a i - 1
            omega)]
      ring

theorem hookProd_eq_E (n : ℕ) (a : ℕ → ℕ) (w : List ℕ) (hw : w.SortedGE)
    (hwe : w = (List.range n).map a) : Formalism.LatticeIndexTer.hookProd (YoungDiagram.ofRowLens w hw) = E n a := by
  subst hwe
  set μ := YoungDiagram.ofRowLens ((List.range n).map a) hw with hμ
  have hmem : ∀ i j, (i, j) ∈ μ ↔ i < n ∧ j < a i := by
    intro i j
    rw [hμ, YoungDiagram.mem_ofRowLens]
    simp
  have hrow : ∀ i < n, μ.rowLen i = a i := by
    intro i hi
    apply eq_of_forall_lt_iff
    intro j
    rw [← YoungDiagram.mem_iff_lt_rowLen, hmem]
    simp [hi]
  have hcol : ∀ c, μ.colLen c = K n a c := by
    intro c
    have e : (range n).filter (fun l => c < a l) = range (μ.colLen c) := by
      ext i
      rw [Finset.mem_filter, Finset.mem_range, Finset.mem_range, ← YoungDiagram.mem_iff_lt_colLen,
        hmem]
    unfold K
    rw [e, Finset.card_range]
  unfold Formalism.LatticeIndexTer.hookProd E
  rw [Finset.prod_finset_product μ.cells (range n) (fun i => range (a i))]
  · refine Finset.prod_congr rfl (fun i hi => Finset.prod_congr rfl (fun c _ => ?_))
    rw [hrow i (Finset.mem_range.mp hi), hcol c]
  · rintro ⟨i, j⟩
    rw [YoungDiagram.mem_cells, hmem]
    simp

end HookLengthProduct

open HookLengthProduct in
theorem hookProd_mul_prod (n : ℕ) (a : ℕ → ℕ) (h1 : ∀ i < n, 1 ≤ a i)
    (hmono : ∀ i l, i < l → l < n → a l ≤ a i) :
    Formalism.LatticeIndexTer.hookProd (YoungDiagram.ofRowLens (((List.range n).map a).insertionSort (· ≥ ·))
              List.sortedGE_insertionSort) *
              (∏ i ∈ Finset.range n, ∏ l ∈ Finset.Ioo i n, (a i + l - a l - i)) =
      ∏ i ∈ Finset.range n, (a i + n - 1 - i).factorial := by
  have hsorted : ((List.range n).map a).insertionSort (· ≥ ·) = (List.range n).map a := by
    apply List.Pairwise.insertionSort_eq
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    simp only [List.length_map, List.length_range] at hi hj
    simp only [List.getElem_map, List.getElem_range]
    exact hmono i j hij hj
  rw [hookProd_eq_E n a _ List.sortedGE_insertionSort hsorted]
  exact E_mul_D n a hmono

end Formalism.MainNotions.DIV.HookProducts
