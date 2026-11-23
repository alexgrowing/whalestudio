import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.SumSplitsEvalTwoWord

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.TB.G2.Gen

open ReciprocityTheory.ChartRestriction.G.TB.G2

variable {k : Type} [CommRing k] {S : Type} [CommRing S] {ι : Type}
  (D : ι → S → S) (κ : k →+* S)
  (hadd : ∀ l f g, D l (f + g) = D l f + D l g) (hC : ∀ l a, D l (κ a) = 0)
  (hmul : ∀ l f g, D l (f * g) = D l f * g + f * D l g)

def TG (w : List ι) (A : S) : S := w.foldr (fun l g => D l g) A

include hadd in
theorem D_zero (l : ι) : D l 0 = 0 := by
  simpa using hadd l 0 0

include hadd in
theorem D_list_sum (l : ι) (L : List S) : D l L.sum = (L.map (D l)).sum := by
  induction L with
  | nil => simpa using D_zero D hadd l
  | cons a L ih => simp [hadd, ih]

theorem TG_append (w w' : List ι) (A : S) : TG D (w ++ w') A = TG D w (TG D w' A) := by
  simp only [TG, List.foldr_append]

include hadd in
theorem TG_add (w : List ι) (A B : S) : TG D w (A + B) = TG D w A + TG D w B := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    show D l (TG D w (A + B)) = D l (TG D w A) + D l (TG D w B)
    rw [ih, hadd]

include hadd hmul in
theorem TG_mul (w : List ι) (A B : S) :
    TG D w (A * B) = ((splits w).map (fun p => TG D p.1 A * TG D p.2 B)).sum := by
  induction w with
  | nil => simp [TG, splits]
  | cons l w ih =>
    have e : ∀ (v : List ι) (X : S), TG D (l :: v) X = D l (TG D v X) := fun _ _ => rfl
    rw [e, ih, D_list_sum D hadd]
    simp only [splits, List.map_append, List.sum_append, List.map_map, Function.comp_def, e, hmul,
      List.sum_map_add]

section Q
variable (e : S →+* k) (c : ι → ι → k) (q : S)
  (hq0 : e q = 0) (hq1 : ∀ l, e (D l q) = 0) (hq2 : ∀ l l', D l (D l' q) = κ (c l l'))

include hadd hC hq2 in
theorem TG_q_long (w : List ι) (hw : 3 ≤ w.length) : TG D w q = 0 := by
  induction w with
  | nil => simp at hw
  | cons l w ih =>
    show D l (TG D w q) = 0
    rcases Nat.lt_or_ge w.length 3 with h | h
    · have h2 : w.length = 2 := by
        simp only [List.length_cons] at hw
        omega
      obtain ⟨y, z, rfl⟩ := List.length_eq_two.mp h2
      show D l (D y (D z q)) = 0
      rw [hq2, hC]
    · rw [ih h, D_zero D hadd]

variable (he : ∀ a, e (κ a) = a)

include hadd hC hq0 hq1 hq2 he in
theorem e_TG_q (b : List ι) : e (TG D b q) = ev2 c b := by
  match b with
  | [] => exact hq0
  | [x] => exact hq1 x
  | [x, y] =>
    show e (D x (D y q)) = c x y
    rw [hq2, he]
  | x :: y :: z :: r =>
    rw [TG_q_long (D := D) (κ := κ) (hadd := hadd) (hC := hC) (c := c) (q := q) (hq2 := hq2)
      (w := x :: y :: z :: r) (by simp)]
    exact map_zero e

include hadd hmul hC hq0 hq1 hq2 he in
theorem e_TG_mul_q (w : List ι) (A : S) :
    e (TG D w (A * q)) = ((splits w).map (fun p => e (TG D p.1 A) * ev2 c p.2)).sum := by
  simp only [TG_mul (D := D) (hadd := hadd) (hmul := hmul), map_list_sum, List.map_map,
    Function.comp_def, map_mul, e_TG_q (D := D) (κ := κ) (hadd := hadd) (hC := hC) (e := e) (c := c)
      (q := q) (hq0 := hq0) (hq1 := hq1) (hq2 := hq2) (he := he)]

end Q

end ReciprocityTheory.ChartRestriction.G.TB.G2.Gen
