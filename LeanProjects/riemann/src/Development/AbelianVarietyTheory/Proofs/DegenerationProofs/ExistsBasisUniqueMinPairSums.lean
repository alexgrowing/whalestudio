import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsReducedBasisOfLinearIndependent

open Module

namespace GlobalTheory

theorem exists_basis_unique_min_pair_sums (X : Type) [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] (q : QuadraticMap ℤ X ℝ)
    (hq : Filter.Tendsto q Filter.cofinite Filter.atTop) (d g N : ℕ) (hd : finrank ℤ X = d)
    (hg : d ≤ g) (hN : 1 + 4 * (g : ℝ) * (2 : ℝ) ^ ((g : ℝ) / 2) < N) :
    ∃ e : Basis (Fin d) ℤ X, ∀ (i j : Fin d) (μ : X), μ ≠ 0 →
      q (e i) < q (e i + N • μ) ∧ q (e i + e j) < q (e i + e j + N • μ) := by
  have hq' := posDef_realExt_of_tendsto q hq
  obtain ⟨e, h1, -, -⟩ := exists_reduced_basis_unique_min_of_le hd hg q hq'
  have hp := posDef_of_posDef_realExt hq'
  set c := (g : ℝ) * (2 : ℝ) ^ ((g : ℝ) / 2) with hc
  have hc0 : 0 ≤ c := by positivity
  have hN' : 1 + 4 * c < ((N : ℤ) : ℝ) := by
    rw [hc, ← mul_assoc]; exact_mod_cast hN
  refine ⟨e, fun i j μ hμ => ?_⟩
  rw [← natCast_zsmul]
  refine ⟨(lt_add_smul_of_abs_polar_le q hc0 (by linarith) (hp μ hμ) (h1 i μ)).1,
    (lt_add_smul_of_abs_polar_le q (c := 2 * c) (by positivity) (by linarith) (hp μ hμ) ?_).1⟩
  rw [QuadraticMap.polar_add_left]
  refine (abs_add_le _ _).trans ?_
  linarith [h1 i μ, h1 j μ]

end GlobalTheory
