import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TCoefMInMMul

noncomputable section

open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A
open scoped ContDiff Topology

namespace GlobalTheory.PsCo.Pc1

theorem iteratedDeriv_scale_eq_zero {G : ℝ → ℝ} (hG : ∀ x, 1 ≤ x → G x = 0) {t : ℝ} (ht : 0 < t) (k : ℕ)
    {x : ℝ} (hx : 1 < t * x) : iteratedDeriv k (fun y => G (t * y)) x = 0 := by
  have hev : (fun y => G (t * y)) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
    have hopen : IsOpen {y : ℝ | 1 < t * y} := isOpen_lt continuous_const (continuous_const.mul continuous_id)
    filter_upwards [hopen.mem_nhds hx] with y hy
    exact hG _ (le_of_lt hy)
  rw [hev.iteratedDeriv_eq k]
  simp [iteratedDeriv_const]

theorem isCutFn_iteratedDeriv_scale {G : ℝ → ℝ} (hGs : ContDiff ℝ ∞ G) (hG : ∀ x, 1 ≤ x → G x = 0) {t : ℝ}
    (ht : 0 < t) (k : ℕ) : IsCutFn (iteratedDeriv k (fun y => G (t * y))) := by
  refine ⟨?_, 2 / t, fun x hx => iteratedDeriv_scale_eq_zero hG ht k ?_⟩
  · rw [iteratedDeriv_eq_iterate]
    exact ContDiff.iterate_deriv k (hGs.comp (contDiff_const.mul contDiff_id))
  · have : 2 ≤ t * x := by rwa [div_le_iff₀ ht, mul_comm] at hx
    linarith

theorem stFam : StFam := by
  intro n ε G p hG
  refine ⟨(Finset.range (nMode ε + 1)).sup fun k => (p k).totalDegree, fun k hk =>
    Finset.le_sup (f := fun k => (p k).totalDegree) (Finset.mem_range.2 (Nat.lt_succ_of_le hk)), fun t ht => ⟨?_, ?_⟩⟩
  · have : famF ε G p t = ∑ k ∈ Finset.range (nMode ε + 1), bas ε (iteratedDeriv k fun x => G (t * x)) (p k) := by
      funext g; simp [famF, Finset.sum_apply]
    rw [this]
    refine Submodule.sum_mem _ fun k hk => Submodule.subset_span ⟨_, p k, isCutFn_iteratedDeriv_scale hG.1 hG.2.1 ht k,
      Finset.le_sup (f := fun k => (p k).totalDegree) hk, rfl⟩
  · intro g hg
    simp only [famF, bas]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [iteratedDeriv_scale_eq_zero hG.2.1 ht k hg]
    simp

end GlobalTheory.PsCo.Pc1
