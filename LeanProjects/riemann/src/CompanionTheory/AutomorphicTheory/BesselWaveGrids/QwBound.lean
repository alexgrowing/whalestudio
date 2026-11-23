import Formalism.HermitianCurvature.StatementD

namespace CompanionTheory.WaveGrid

open Formalism.FourierDecayAlt

noncomputable def fac (l : C.Letter) (y : ℝ) : ℝ :=
  if l.1 then (y - l.2 + 1) / (y - l.2) else (l.2 - y) / (l.2 - y - 1)

noncomputable def facW {S : Type} (l : Wd.Letter ℂ S) (Y : ℂ) : ℂ :=
  if l.plus then (Y - l.pt + 1) / (Y - l.pt) else (l.pt - Y) / (l.pt - Y - 1)

theorem qw_eq_prod {S : Type} [Fintype S] [DecidableEq S] (q : ℂ → ℂ) (L : List (Wd.Letter ℂ S)) (Y : ℂ) :
    Wd.qw q L Y = q Y * (L.map fun l => facW l Y).prod := by
  induction L with
  | nil => simp [Wd.qw]
  | cons l L ih =>
    by_cases h : l.plus
    · simp only [Wd.qw, h, if_true, List.map_cons, List.prod_cons, ih, facW]
      ring
    · simp only [Wd.qw, h, List.map_cons, List.prod_cons, ih, facW]
      simp only [Bool.false_eq_true, if_false]
      ring

theorem positioned_map_facW (w : List C.Letter) (y : ℝ) :
    (D.positionted w).map (fun l => facW l (y : ℂ)) = w.map fun l => ((fac l y : ℝ) : ℂ) := by
  apply List.ext_getElem
  · simp [D.positionted]
  · intro n h1 h2
    simp only [D.positionted, List.getElem_map, List.getElem_ofFn, facW, fac]
    by_cases h : (w[n]'(by simpa using h2)).1
    · simp [h]
    · simp [h]

theorem ofReal_prod_map (w : List C.Letter) (f : C.Letter → ℝ) :
    (((w.map f).prod : ℝ) : ℂ) = (w.map fun l => ((f l : ℝ) : ℂ)).prod := by
  induction w with
  | nil => simp
  | cons l w ih => simp [ih]

theorem qC_ofReal (P : M.Par) (y : ℝ) :
    M.qC P (y : ℂ) = ((I.qpoly P.k P.T P.T' P.u P.u' y : ℝ) : ℂ) := by
  simp [M.qC, I.qpoly]

theorem qw_indexed_ofReal (P : M.Par) (w : List C.Letter) (y : ℝ) :
    Wd.qw (M.qC P) (D.positionted w) (y : ℂ) =
      ((I.qpoly P.k P.T P.T' P.u P.u' y * (w.map fun l => fac l y).prod : ℝ) : ℂ) := by
  rw [qw_eq_prod, positioned_map_facW, qC_ofReal, Complex.ofReal_mul]
  congr 1
  exact (ofReal_prod_map w fun l => fac l y).symm

theorem fac_ge (l : C.Letter) (y : ℝ) (h : 4 ≤ |y - l.2|) : 3 / 4 ≤ fac l y := by
  unfold fac
  split_ifs
  · rcases le_abs'.1 h with h' | h'
    · have hneg : y - l.2 < 0 := by linarith
      rw [le_div_iff_of_neg hneg]
      linarith
    · have hpos : 0 < y - l.2 := by linarith
      rw [le_div_iff₀ hpos]
      linarith
  · rcases le_abs'.1 h with h' | h'
    · have hpos : 0 < l.2 - y - 1 := by linarith
      rw [le_div_iff₀ hpos]
      linarith
    · have hneg : l.2 - y - 1 < 0 := by linarith
      rw [le_div_iff_of_neg hneg]
      linarith

theorem prod_fac_ge (w : List C.Letter) (y : ℝ) (h : ∀ l ∈ w, 4 ≤ |y - l.2|) :
    (3 / 4 : ℝ) ^ w.length ≤ (w.map fun l => fac l y).prod := by
  induction w with
  | nil => simp
  | cons l w ih =>
    simp only [List.length_cons, List.map_cons, List.prod_cons, pow_succ]
    have h1 := fac_ge l y (h l (by simp))
    have h2 := ih fun l' hl' => h l' (by simp [hl'])
    rw [mul_comm]
    exact mul_le_mul h1 h2 (by positivity) (by linarith)

theorem qw_re_ge (P : M.Par) (w : List C.Letter) (y : ℝ) (hq : 0 ≤ I.qpoly P.k P.T P.T' P.u P.u' y)
    (h : ∀ l ∈ w, 4 ≤ |y - l.2|) :
    (3 / 4 : ℝ) ^ w.length * I.qpoly P.k P.T P.T' P.u P.u' y ≤ (Wd.qw (M.qC P) (D.positionted w) (y : ℂ)).re := by
  rw [qw_indexed_ofReal, Complex.ofReal_re, mul_comm]
  exact mul_le_mul_of_nonneg_left (prod_fac_ge w y h) hq

theorem qw_re_pos (P : M.Par) (w : List C.Letter) (y : ℝ) (hq : 0 < I.qpoly P.k P.T P.T' P.u P.u' y)
    (h : ∀ l ∈ w, 4 ≤ |y - l.2|) : 0 < (Wd.qw (M.qC P) (D.positionted w) (y : ℂ)).re :=
  lt_of_lt_of_le (by positivity) (qw_re_ge P w y hq.le h)

end CompanionTheory.WaveGrid
