import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzContinuousAtOfPointwiseOfBounded

open SchwartzMap Filter Topology
open scoped ContDiff

namespace GlobalTheory

lemma norm_iteratedFDeriv_comp_smul_le_seminorm {V : Type} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (ψ : SchwartzMap V ℂ) {t : ℝ} (ht : |t| ≤ 1) (i : ℕ) (x : V) :
    ‖iteratedFDeriv ℝ i (fun y : V => ψ (t • y)) x‖ ≤ SchwartzMap.seminorm ℝ 0 i ψ := by
  have e : (fun y : V => ψ (t • y)) = ψ ∘ (t • ContinuousLinearMap.id ℝ V) := by
    funext y; simp
  rw [e, ContinuousLinearMap.iteratedFDeriv_comp_right _ (ψ.smooth ⊤) x
    (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have h1 : ∏ _j : Fin i, ‖(t • ContinuousLinearMap.id ℝ V)‖ ≤ 1 :=
    Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => by
      refine (norm_smul_le _ _).trans ?_
      rw [Real.norm_eq_abs]
      exact mul_le_one₀ ht (norm_nonneg _) ContinuousLinearMap.norm_id_le)
  refine (mul_le_of_le_one_right (norm_nonneg _) h1).trans ?_
  exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ ψ i _

theorem dense_hasCompactSupport_schwartz : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V], Dense {φ : SchwartzMap V ℂ | HasCompactSupport (⇑φ)} := by
  intro V _ _ _
  let b : ContDiffBump (0 : V) := ⟨1, 2, one_pos, one_lt_two⟩
  have hbc : HasCompactSupport (fun x : V => (b x : ℂ)) :=
    b.hasCompactSupport.comp_left Complex.ofReal_zero
  have hbs : ContDiff ℝ ∞ (fun x : V => (b x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp b.contDiff
  let ψ : SchwartzMap V ℂ := hbc.toSchwartzMap hbs
  have hψ : ∀ x, ψ x = (b x : ℂ) := fun x => rfl
  have hψ0 : ψ 0 = 1 := by
    rw [hψ, b.one_of_mem_closedBall (by simp [b])]; simp
  have hg : ∀ t : ℝ, Function.HasTemperateGrowth (fun x : V => ψ (t • x)) := fun t =>
    ψ.hasTemperateGrowth.comp (t • ContinuousLinearMap.id ℝ V).hasTemperateGrowth
  intro φ
  let F : ℝ → SchwartzMap V ℂ := fun t => SchwartzMap.smulLeftCLM ℂ (fun x : V => ψ (t • x)) φ
  have hF : ∀ t x, F t x = ψ (t • x) * φ x := fun t x => by
    simp only [F, SchwartzMap.smulLeftCLM_apply_apply (hg t), smul_eq_mul]
  have hFf : ∀ t, (⇑(F t) : V → ℂ) = fun x => ψ (t • x) * φ x := fun t => funext (hF t)
  have hF0 : F 0 = φ := by ext x; rw [hF]; simp [hψ0]
  have hcs : ∀ t : ℝ, t ≠ 0 → HasCompactSupport (⇑(F t)) := fun t ht => by
    rw [hFf]
    exact (hbc.comp_homeomorph (Homeomorph.smulOfNeZero t ht)).mul_right
  have hcont : ContinuousAt F 0 := by
    refine schwartz_continuousAt_of_pointwise_of_bounded F 0 (fun v => ?_) (fun k n => ?_)
    · simp_rw [hF]
      exact ((ψ.continuous.comp (continuous_id.smul continuous_const)).mul
        continuous_const).continuousAt
    · refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * SchwartzMap.seminorm ℝ 0 i ψ *
        SchwartzMap.seminorm ℝ k (n - i) φ, ?_⟩
      have hball : Set.Icc (-1 : ℝ) 1 ∈ 𝓝 (0 : ℝ) := Icc_mem_nhds (by norm_num) (by norm_num)
      filter_upwards [hball] with t ht v
      have ht' : |t| ≤ 1 := abs_le.2 ht
      rw [hFf]
      have hsm1 : ContDiff ℝ ∞ (fun x : V => ψ (t • x)) :=
        (ψ.smooth ⊤).comp (contDiff_const_smul t)
      refine (mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_mul_le hsm1 (φ.smooth ⊤) v
        (by exact_mod_cast le_top)) (by positivity)).trans ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      have h1 := norm_iteratedFDeriv_comp_smul_le_seminorm ψ ht' i v
      have h2 := SchwartzMap.le_seminorm ℝ k (n - i) φ v
      calc ‖v‖ ^ k * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun x => ψ (t • x)) v‖ *
            ‖iteratedFDeriv ℝ (n - i) (⇑φ) v‖)
          = (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun x => ψ (t • x)) v‖ *
            (‖v‖ ^ k * ‖iteratedFDeriv ℝ (n - i) (⇑φ) v‖) := by ring
        _ ≤ _ := by gcongr
  have hT : Tendsto F (𝓝[≠] 0) (𝓝 φ) := by
    rw [← hF0]; exact hcont.tendsto.mono_left nhdsWithin_le_nhds
  exact mem_closure_of_tendsto hT (eventually_nhdsWithin_of_forall fun t ht => hcs t ht)

end GlobalTheory
