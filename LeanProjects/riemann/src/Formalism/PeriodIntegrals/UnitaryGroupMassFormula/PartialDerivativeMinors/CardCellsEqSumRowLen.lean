import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PartialDerivativeMinors.PMinorAff

noncomputable section

open scoped BigOperators
open Classical

namespace PI.EntAtD.W

open PI.EntAtD Formalism.BasicNotions Formalism.MainNotions.G

theorem card_cells_eq_sum_rowLen (α : YoungDiagram) (n : ℕ) (h : ∀ r, n ≤ r → α.rowLen r = 0) :
    α.cells.card = ∑ r ∈ Finset.range n, α.rowLen r := by
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := Finset.range n)]
  · refine Finset.sum_congr rfl fun r _ => ?_
    rw [YoungDiagram.rowLen_eq_card]
    first
      | rfl
      | (simp only [YoungDiagram.row]; congr 1)
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_range] at hx ⊢
    by_contra hc
    have h0 := h x.1 (not_lt.mp hc)
    have hx' : (x.1, x.2) ∈ α := hx
    rw [YoungDiagram.mem_iff_lt_rowLen] at hx'
    omega

theorem cPr_le_ctD (D : D7) (u : D.what₂.Word) (i : ℕ) (nu : Pl D → YoungDiagram)
    (hrow : ∀ z r, (((nu z).rowLen r : ℕ) : ℝ) =
      if r < D.R.N i then DV.nuRow D u (i + 1) (tauPl D z) r else 0)
    (hN : 2 ≤ D.R.N i) (t : HH D) :
    (cPr (nu (false, t)) (nu (true, t)) : ℝ) ≤ ctD D u (i + 1) t := by
  have hN0 : 0 < D.R.N i := by omega
  have hN1 : 1 < D.R.N i := by omega

  have hr : ∀ z r, r < D.R.N i → DV.nuRow D u (i + 1) (tauPl D z) r = ((nu z).rowLen r : ℝ) := by
    intro z r hr'
    rw [hrow z r, if_pos hr']
  have hz : ∀ z r, D.R.N i ≤ r → (nu z).rowLen r = 0 := by
    intro z r hr'
    have hz0 := hrow z r
    rw [if_neg (by omega)] at hz0
    exact_mod_cast hz0
  have hsum := card_cells_eq_sum_rowLen (nu (false, t)) (D.R.N i) (hz _)
  have habs : nuAbs D u (i + 1) (tauPl D (false, t)) = ((nu (false, t)).cells.card : ℝ) := by
    rw [hsum]
    unfold nuAbs
    rw [Nat.add_sub_cancel]
    push_cast
    refine Finset.sum_congr rfl fun r hr' => ?_
    exact hr _ r (Finset.mem_range.mp hr')
  have h0le : (nu (false, t)).rowLen 0 ≤ (nu (false, t)).cells.card := by
    rw [hsum]
    exact Finset.single_le_sum (f := fun r => (nu (false, t)).rowLen r)
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hN0)
  unfold cPr ctD
  rw [habs, hr (false, t) 0 hN0, hr (false, t) 1 hN1, hr (true, t) 0 hN0]
  push_cast [Nat.cast_sub h0le]
  have hm1 := min_le_left ((nu (false, t)).rowLen 0 : ℝ) ((nu (true, t)).rowLen 0 : ℝ)
  have hm2 := min_le_right ((nu (false, t)).rowLen 0 : ℝ) ((nu (true, t)).rowLen 0 : ℝ)
  have ha1 : (0 : ℝ) ≤ ((nu (false, t)).rowLen 1 : ℝ) := Nat.cast_nonneg _
  split_ifs <;> linarith

theorem entAtD_of_core (h : CoreBound) : PI.EntAtD.EntAtD := by
  unfold PI.EntAtD.EntAtD
  intro D Dx nu hrow hcol Th hTh u μ w hLF hram i hi L L'
  have hS := hTh u μ w hLF hram i hi L L'
  have hc := h (HH D) (D.R.N i) (D.R.N (i + 1)) (D.what₂.places.resChar w) (nu u i)
    (Th u μ w i L L') hS
  have hN : 2 ≤ D.R.N i := by
    show 2 ≤ D.R.k + i * (D.R.t + 1)
    have h2 := D.R.two_le_m
    have h3 := D.R.m_add_three_le_k
    exact le_trans (by omega : 2 ≤ D.R.k) (Nat.le_add_right _ _)

  have hle : ∑ t : HH D, (cPr (nu u i (false, t)) (nu u i (true, t)) : ℝ) ≤
      ∑ t : HH D, ctD D u (i + 1) t :=
    Finset.sum_le_sum fun t _ => cPr_le_ctD D u i (nu u i) (hrow u i hi) hN t
  have hp : (1 : ℝ) ≤ (D.what₂.places.resChar w : ℝ) := by
    have hpr : (D.what₂.places.resChar w).Prime := Fact.out
    exact_mod_cast hpr.one_lt.le
  unfold KvalGe at hc ⊢
  intro I m
  refine (hc I m).trans ?_
  apply Real.rpow_le_rpow_of_exponent_le hp
  linarith

end PI.EntAtD.W
