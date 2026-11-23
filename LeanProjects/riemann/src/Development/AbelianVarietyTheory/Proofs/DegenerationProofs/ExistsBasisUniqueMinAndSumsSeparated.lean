import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsReducedBasisOfLinearIndependent

open Module

namespace GlobalTheory

theorem eq_zero_of_sum_eq_sum_add_nsmul {X : Type*} [AddCommGroup X] {ι : Type*}
    (e : Basis ι ℤ X) {C : ℝ} (hC : 0 ≤ C) {N' D k : ℕ} (hN' : 2 * (D : ℝ) * C < N') (hk : k ≤ D)
    (α β : Fin k → X) (hα : ∀ j i, |(e.repr (α j) i : ℝ)| ≤ C)
    (hβ : ∀ j i, |(e.repr (β j) i : ℝ)| ≤ C) (w : X)
    (h : ∑ j, α j = ∑ j, β j + N' • w) : w = 0 := by
  refine e.repr.injective (Finsupp.ext fun i => ?_)
  have h1 : ∑ j, (e.repr (α j) i : ℝ) = ∑ j, (e.repr (β j) i : ℝ) + N' * (e.repr w i : ℝ) := by
    have := congrArg (fun x => e.repr x i) h
    simp only [map_add, map_sum, map_nsmul, Finsupp.coe_add, Pi.add_apply, Finsupp.coe_finsetSum,
      Finset.sum_apply, Finsupp.coe_smul, Pi.smul_apply, nsmul_eq_mul] at this
    exact_mod_cast this
  have bound : ∀ γ : Fin k → X, (∀ j i, |(e.repr (γ j) i : ℝ)| ≤ C) →
      |∑ j, (e.repr (γ j) i : ℝ)| ≤ D * C := fun γ hγ => by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun j _ => hγ j i).trans ?_)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hC
  have hA := abs_le.1 (bound α hα)
  have hB := abs_le.1 (bound β hβ)
  have hpos : (0 : ℝ) < N' := lt_of_le_of_lt (by positivity) hN'
  have h2 : (e.repr w i : ℝ) < 1 := by
    by_contra hc
    have := mul_le_mul_of_nonneg_left (not_lt.1 hc) hpos.le
    linarith [hA.2, hB.1]
  have h3 : (-1 : ℝ) < (e.repr w i : ℝ) := by
    by_contra hc
    have := mul_le_mul_of_nonneg_left (not_lt.1 hc) hpos.le
    linarith [hA.1, hB.2]
  have h2' : e.repr w i < 1 := by exact_mod_cast h2
  have h3' : -1 < e.repr w i := by exact_mod_cast h3
  simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply]
  omega

theorem exists_basis_unique_min_and_sums_separated :
    ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (q : QuadraticMap ℤ X ℝ), Filter.Tendsto q Filter.cofinite Filter.atTop → ∀ (d g N N' D : ℕ), finrank ℤ X = d → d ≤ g → 1 + 2 * (g : ℝ) * (2 : ℝ) ^ ((g : ℝ) / 2) < N → 2 * (D : ℝ) * ((g : ℝ) * (3 / 2 : ℝ) ^ g * (2 : ℝ) ^ ((g : ℝ) / 2 - 1)) * N < N' → ∃ e : Basis (Fin d) ℤ X, (∀ (i : Fin d) (μ : X), μ ≠ 0 → q (e i) < q (e i + N • μ) ∧ q (-e i) < q (-e i + N • μ)) ∧ ∀ (k : ℕ) (α β : Fin k → X), k ≤ D → (∀ j w, q (α j) ≤ q (α j + N • w)) → (∀ j w, q (β j) ≤ q (β j + N • w)) → ∀ w : X, ∑ j, α j = ∑ j, β j + N' • w → w = 0 := by
  intro X _ _ _ q hq d g N N' D hd hg hN hN'
  obtain ⟨e, -, h2, h3⟩ :=
    exists_reduced_basis_unique_min_of_le hd hg q (posDef_realExt_of_tendsto q hq)
  have h0 : (0 : ℝ) ≤ 2 * (g : ℝ) * (2 : ℝ) ^ ((g : ℝ) / 2) := by positivity
  have hN1 : (1 : ℤ) ≤ (N : ℤ) := by
    have : (1 : ℝ) ≤ N := by linarith
    exact_mod_cast this
  refine ⟨e, fun i μ hμ => ?_, fun k α β hk hα hβ w h => ?_⟩
  · have := h3 (N : ℤ) (by push_cast; linarith) i μ hμ
    simpa only [natCast_zsmul] using this
  · have key : ∀ γ : Fin k → X, (∀ j w, q (γ j) ≤ q (γ j + N • w)) → ∀ j i,
        |(e.repr (γ j) i : ℝ)| ≤
          (g : ℝ) * (3 / 2 : ℝ) ^ g * (2 : ℝ) ^ ((g : ℝ) / 2 - 1) * N := fun γ hγ j i => by
      have := h2 (N : ℤ) hN1 (γ j) (fun w => by simpa only [natCast_zsmul] using hγ j w) i
      simpa only [Int.cast_natCast] using this
    exact eq_zero_of_sum_eq_sum_add_nsmul e (by positivity) (by linarith) hk α β
      (key α hα) (key β hβ) w h

end GlobalTheory
