import Mathlib
import Formalism.PeriodIntegrals.JointBlockShapes.MinusPart
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockRaisingLowering.SameSign

noncomputable section

namespace FockRaiseLowGrade

open MvPolynomial FockH1Action

variable {σ : Type*}

theorem hc_hc (m n : ℕ) (P : MvPolynomial σ ℂ) :
    homogeneousComponent m (homogeneousComponent n P) =
      if m = n then homogeneousComponent n P else 0 := by
  classical
  rw [homogeneousComponent_of_mem (homogeneousComponent_mem n P)]

theorem eq_zero_of_hc (x : MvPolynomial σ ℂ) (h : ∀ e, homogeneousComponent e x = 0) :
    x = 0 := by
  calc x = ∑ i ∈ Finset.range (x.totalDegree + 1), homogeneousComponent i x :=
        (sum_homogeneousComponent x).symm
    _ = 0 := Finset.sum_eq_zero (fun i _ => h i)

theorem sum_hc_of_le (P : MvPolynomial σ ℂ) (n : ℕ) (hn : P.totalDegree < n) :
    ∑ i ∈ Finset.range n, homogeneousComponent i P = P := by
  have hsub : Finset.range (P.totalDegree + 1) ⊆ Finset.range n := by
    intro i hi
    simp only [Finset.mem_range] at hi ⊢
    omega
  rw [← Finset.sum_subset hsub ?_]
  · exact sum_homogeneousComponent P
  · intro i _ hi
    simp only [Finset.mem_range, not_lt] at hi
    apply homogeneousComponent_eq_zero
    omega

theorem plus_eq (R L : Module.End ℂ (MvPolynomial σ ℂ))
    (hR : ∀ (d : ℕ) (P : MvPolynomial σ ℂ), P ∈ homog σ d → R P ∈ homog σ (d + 2))
    (hL : ∀ (e : ℕ) (P : MvPolynomial σ ℂ),
      homogeneousComponent e (L P) = L (homogeneousComponent (e + 2) P))
    (P : MvPolynomial σ ℂ) : plusPart (R + L) P = R P := by
  classical
  have hterm : ∀ d, homogeneousComponent (d + 2) ((R + L) (homogeneousComponent d P)) =
      R (homogeneousComponent d P) := by
    intro d
    have hmem := hR d _ (homogeneousComponent_mem d P)
    rw [LinearMap.add_apply, map_add, hL, hc_hc,
      if_neg (show ¬ (d + 2 + 2 = d) by omega), map_zero, add_zero,
      homogeneousComponent_of_mem hmem, if_pos rfl]
  have hsupp : (Function.support fun d => R (homogeneousComponent d P)) ⊆
      ↑(Finset.range (P.totalDegree + 1)) := by
    intro d hd
    rw [Function.mem_support] at hd
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra hlt
    apply hd
    have h0 : homogeneousComponent d P = 0 := by
      apply homogeneousComponent_eq_zero
      omega
    rw [h0, map_zero]
  rw [FockH1Action.plusPart, finsum_congr hterm, finsum_eq_sum_of_support_subset _ hsupp,
    ← map_sum R, sum_homogeneousComponent]

private theorem apply_homogeneousComponent_eq_zero_of_lt_two (L : Module.End ℂ (MvPolynomial σ ℂ))
    (hL : ∀ (e : ℕ) (P : MvPolynomial σ ℂ),
      homogeneousComponent e (L P) = L (homogeneousComponent (e + 2) P))
    (Q : MvPolynomial σ ℂ) (k : ℕ) (hk : k < 2) : L (homogeneousComponent k Q) = 0 := by
  apply eq_zero_of_hc
  intro e
  rw [hL, hc_hc, if_neg (show ¬ (e + 2 = k) by omega), map_zero]

theorem minus_eq (R L : Module.End ℂ (MvPolynomial σ ℂ))
    (hR : ∀ (d : ℕ) (P : MvPolynomial σ ℂ), P ∈ homog σ d → R P ∈ homog σ (d + 2))
    (hL : ∀ (e : ℕ) (P : MvPolynomial σ ℂ),
      homogeneousComponent e (L P) = L (homogeneousComponent (e + 2) P))
    (P : MvPolynomial σ ℂ) : minusPart (R + L) P = L P := by
  classical
  have hterm : ∀ d, homogeneousComponent d ((R + L) (homogeneousComponent (d + 2) P)) =
      L (homogeneousComponent (d + 2) P) := by
    intro d
    have hmem := hR (d + 2) _ (homogeneousComponent_mem (d + 2) P)
    rw [LinearMap.add_apply, map_add, hL, hc_hc, if_pos rfl,
      homogeneousComponent_of_mem hmem]
    split_ifs with hc
    · exact absurd hc (by omega)
    · rw [zero_add]
  have hsupp : (Function.support fun d => L (homogeneousComponent (d + 2) P)) ⊆
      ↑(Finset.range (P.totalDegree + 1)) := by
    intro d hd
    rw [Function.mem_support] at hd
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra hlt
    apply hd
    have h0 : homogeneousComponent (d + 2) P = 0 := by
      apply homogeneousComponent_eq_zero
      omega
    rw [h0, map_zero]
  rw [FockH1Action.minusPart, finsum_congr hterm, finsum_eq_sum_of_support_subset _ hsupp]
  calc ∑ d ∈ Finset.range (P.totalDegree + 1), L (homogeneousComponent (d + 2) P)
      = ∑ i ∈ Finset.range (P.totalDegree + 1 + 1 + 1), L (homogeneousComponent i P) := by
        rw [Finset.sum_range_succ' _ (P.totalDegree + 1 + 1),
          Finset.sum_range_succ' _ (P.totalDegree + 1),
          apply_homogeneousComponent_eq_zero_of_lt_two L hL P 0 (by norm_num)]
        simp only [zero_add, apply_homogeneousComponent_eq_zero_of_lt_two L hL P 1 (by norm_num), add_zero]
        try rfl
    _ = L P := by
        rw [← map_sum L, sum_hc_of_le P (P.totalDegree + 1 + 1 + 1) (by omega)]

theorem raisingLoweringSplit : FockRL.PMSplit := by
  intro σ R L hR hL P
  exact ⟨plus_eq R L hR hL P, minus_eq R L hR hL P⟩

end FockRaiseLowGrade
