import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
open GlobalTheory.Poinc
open Classical

namespace GlobalTheory.UPoinc

theorem classSum_norm_eq_of_unique_least : ∀ (p : ℕ) [Fact p.Prime] (X Y : Type) [AddCommGroup X] [AddCommGroup Y] (e : X ≃+ Y) (β : LinearMap.BilinForm ℤ X) (be : LinearMap.BilinForm ℤ Y) (sc sc' : ℝ), 0 < sc → (∀ a b, sc * (β a b : ℝ) = sc' * (be (e a) (e b) : ℝ)) → ∀ (m : ℕ) (t : Y → PadicAlgCl p), (∀ μ, ‖t μ‖ ≤ Real.exp (-(sc' * (be μ μ : ℝ) / 2))) → ∀ (v : PadicAlgCl p) (ν : Y), (∀ δ : ℝ, 0 < δ → ∃ S₀ : Finset Y, ∀ S : Finset Y, (∀ μ ∈ S, CongMod m μ ν) → (∀ μ ∈ S₀, CongMod m μ ν → μ ∈ S) → ‖v - ∑ μ ∈ S, t μ‖ ≤ δ) → ∀ μ : X, CongMod m (e μ) ν → ‖t (e μ)‖ = Real.exp (-(sc' * (be (e μ) (e μ) : ℝ) / 2)) → (∀ μ' : X, CongMod m μ' μ → μ' ≠ μ → β μ μ < β μ' μ') → ‖v‖ = Real.exp (-(sc * (β μ μ : ℝ)) / 2) := by
  intro p _ X Y _ _ e β be sc sc' hsc hid m t ht v ν hv μ hμν htμ hmin
  have hR' : ‖t (e μ)‖ = Real.exp (-(sc * (β μ μ : ℝ)) / 2) := by
    rw [htμ, hid μ μ]; congr 1; ring
  have hlt1 : Real.exp (-(sc * ((β μ μ : ℝ) + 1)) / 2) < Real.exp (-(sc * (β μ μ : ℝ)) / 2) :=
    Real.exp_lt_exp.2 (by nlinarith)
  have hbound : ∀ y : Y, CongMod m y ν → y ≠ e μ →
      ‖t y‖ ≤ Real.exp (-(sc * ((β μ μ : ℝ) + 1)) / 2) := by
    intro y h1 h2
    obtain ⟨w1, hw1⟩ := h1
    obtain ⟨w2, hw2⟩ := hμν
    have hx : CongMod m (e.symm y) μ := by
      refine ⟨e.symm (w1 - w2), ?_⟩
      apply e.injective
      rw [e.apply_symm_apply, map_add, map_nsmul, e.apply_symm_apply, hw1, hw2, smul_sub]
      abel
    have hne : e.symm y ≠ μ := by
      intro h; apply h2; rw [← h, e.apply_symm_apply]
    have hlt := Int.add_one_le_of_lt (hmin (e.symm y) hx hne)
    have hle : (β μ μ : ℝ) + 1 ≤ (β (e.symm y) (e.symm y) : ℝ) := by exact_mod_cast hlt
    calc ‖t y‖ ≤ Real.exp (-(sc' * (be y y : ℝ) / 2)) := ht y
      _ = Real.exp (-(sc * (β (e.symm y) (e.symm y) : ℝ)) / 2) := by
          have h3 := hid (e.symm y) (e.symm y)
          rw [e.apply_symm_apply] at h3
          rw [h3]; congr 1; ring
      _ ≤ Real.exp (-(sc * ((β μ μ : ℝ) + 1)) / 2) := Real.exp_le_exp.2 (by nlinarith)
  have hRpos : 0 < Real.exp (-(sc * (β μ μ : ℝ)) / 2) := Real.exp_pos _
  obtain ⟨S₀, hS₀⟩ := hv (Real.exp (-(sc * (β μ μ : ℝ)) / 2) / 2) (by positivity)
  have hSc : ∀ x ∈ insert (e μ) (S₀.filter (fun x => CongMod m x ν)), CongMod m x ν := by
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact hμν
    · exact (Finset.mem_filter.1 hx).2
  have hclose := hS₀ (insert (e μ) (S₀.filter (fun x => CongMod m x ν))) hSc
    (fun x hx hc => Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨hx, hc⟩))
  set S := insert (e μ) (S₀.filter (fun x => CongMod m x ν)) with hSdef
  have hsum : ∑ x ∈ S, t x = t (e μ) + ∑ x ∈ S.erase (e μ), t x :=
    (Finset.add_sum_erase S t (Finset.mem_insert_self _ _)).symm
  have hrest : ‖∑ x ∈ S.erase (e μ), t x‖ ≤ Real.exp (-(sc * ((β μ μ : ℝ) + 1)) / 2) := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (Real.exp_pos _).le
    intro x hx
    exact hbound x (hSc x (Finset.mem_of_mem_erase hx)) (Finset.ne_of_mem_erase hx)
  have hnS : ‖∑ x ∈ S, t x‖ = Real.exp (-(sc * (β μ μ : ℝ)) / 2) := by
    rw [hsum, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hR']; linarith), hR']
    exact max_eq_left (by linarith)
  have hv' : v = (v - ∑ x ∈ S, t x) + ∑ x ∈ S, t x := by abel
  rw [hv', IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hnS]; linarith), hnS]
  exact max_eq_right (by linarith)

end GlobalTheory.UPoinc
