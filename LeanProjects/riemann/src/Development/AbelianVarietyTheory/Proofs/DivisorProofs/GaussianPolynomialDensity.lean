import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzTendstoOfPointwiseUniformBoundsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzTaylorSeriesConvergesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzTaylorPartialSumDerivBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussianQuadraticFormSchwartzBoundsStatement
open SchwartzMap Filter Topology
open scoped Nat

namespace GlobalTheory

theorem gaussian_mul_mem_closure_of_taylor : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (Q : V →ₗ[ℝ] V →ₗ[ℝ] ℂ) (c : ℝ), 0 < c → (∀ x, c * ‖x‖ ^ 2 ≤ (Q x x).re) →
    ∀ g : SchwartzMap V ℂ, (∀ x, g x = Complex.exp (-(Q x x))) →
    ∀ N : Submodule ℂ (SchwartzMap V ℂ),
    (∀ (j : ℕ) (M : ContinuousMultilinearMap ℝ (fun _ : Fin j => V) ℂ),
      ∃ f ∈ N, ∀ x, f x = M (fun _ => x) * g x) →
    ∀ (ψ : SchwartzMap V ℂ) (A ρ : ℝ), (∀ (j : ℕ) (y : V), ‖iteratedFDeriv ℝ j ψ y‖ ≤ A * ρ ^ j) →
    ∀ F : SchwartzMap V ℂ, (∀ x, F x = ψ x * g x) → F ∈ N.topologicalClosure := by
  intro V _ _ _ Q c hc hQ g hg N hN ψ A ρ hψ F hF
  set p : ℕ → V → ℂ := fun m y => ∑ j ∈ Finset.range (m + 1),
      ((j ! : ℝ))⁻¹ • iteratedFDeriv ℝ j ψ 0 (fun _ => y) with hp
  choose f hfN hf using fun j => hN j (((j ! : ℝ))⁻¹ • iteratedFDeriv ℝ j ψ 0)
  set Fm : ℕ → SchwartzMap V ℂ := fun m => ∑ j ∈ Finset.range (m + 1), f j with hFm
  have hFmN : ∀ m, Fm m ∈ N := fun m => Submodule.sum_mem _ fun j _ => hfN j
  have hFmx : ∀ m x, Fm m x = p m x * g x := by
    intro m x
    simp only [hFm, hp, Finset.sum_mul]
    rw [SchwartzMap.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hf j x]; rfl
  have hFmfun : ∀ m, (⇑(Fm m) : V → ℂ) = fun y => p m y * g y := fun m => funext (hFmx m)
  have hgfun : (⇑g : V → ℂ) = fun y => Complex.exp (-(Q y y)) := funext hg
  have hpcd : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (p m) := by
    intro m
    refine ContDiff.sum fun j _ => ?_
    exact ((iteratedFDeriv ℝ j ψ 0).contDiff.comp (contDiff_pi.2 fun _ => contDiff_id)).const_smul _
  have hT : Tendsto Fm atTop (𝓝 F) := by
    refine GlobalTheory.T.schwartz_tendsto_of_pointwise_uniform_bounds Fm F (fun v => ?_) (fun k n => ?_)
    · simp only [hFmx, hF]
      exact (GlobalTheory.T.schwartz_taylor_series_converges ψ A ρ hψ v).mul_const _
    · choose C hC using fun i => GlobalTheory.T.gaussian_quadratic_form_schwartz_bounds Q c hc hQ i k |ρ|
      refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (|A| * |ρ| ^ i) * C (n - i), fun m v => ?_⟩
      rw [hFmfun]
      refine (mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_mul_le (hpcd m) (g.smooth ⊤) v
        (by exact_mod_cast le_top)) (by positivity)).trans ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      have h2 := GlobalTheory.T.schwartz_taylor_partial_sum_deriv_bound ψ A ρ hψ m i v
      have h3 := hC (n - i) v
      rw [← hgfun] at h3
      calc ‖v‖ ^ k * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (p m) v‖ * ‖iteratedFDeriv ℝ (n - i) g v‖)
          ≤ ‖v‖ ^ k * ((n.choose i : ℝ) * (|A| * |ρ| ^ i * Real.exp (|ρ| * ‖v‖)) *
              ‖iteratedFDeriv ℝ (n - i) g v‖) := by gcongr
        _ = (n.choose i : ℝ) * (|A| * |ρ| ^ i) *
              (‖v‖ ^ k * Real.exp (|ρ| * ‖v‖) * ‖iteratedFDeriv ℝ (n - i) g v‖) := by ring
        _ ≤ _ := by gcongr
  have : F ∈ closure (N : Set (SchwartzMap V ℂ)) :=
    mem_closure_of_tendsto hT (Eventually.of_forall hFmN)
  rw [← Submodule.topologicalClosure_coe] at this
  exact this

end GlobalTheory
