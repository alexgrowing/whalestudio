import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn

open Metric Set Filter
open scoped Topology ContDiff

namespace GlobalTheory.HoloNormed

theorem differentiableOn_fderiv {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] {f : E → V} {U : Set E} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) : DifferentiableOn ℂ (fderiv ℂ f) U := by
  intro c hc
  obtain ⟨R, hR, M, hRU, hM⟩ := SCV.exists_ball_bound hU hf hc
  set r := R / 2 with hr
  have hr0 : 0 < r := by positivity
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM c (mem_ball_self hR))
  have hsub : ∀ x ∈ ball c r, ball x r ⊆ ball c R := fun x hx =>
    ball_subset_ball' (by linarith [mem_ball.mp hx])
  have hrU : ball c r ⊆ U := (ball_subset_ball (by linarith)).trans hRU
  set C := 2 * M / r with hC
  have hC0 : 0 ≤ C := by positivity
  have hb : ∀ v, ∀ x ∈ ball c r, ‖fderiv ℂ f x v‖ ≤ C * ‖v‖ := fun v x hx =>
    (fderiv ℂ f x).le_of_opNorm_le (SCV.norm_fderiv_le_of_ball hr0 (hf.mono ((hsub x hx).trans hRU))
      fun z hz => hM z (hsub x hx hz)) v
  have hd : ∀ v, DifferentiableOn ℂ (fun x => fderiv ℂ f x v) U := SCV.differentiableOn_fderiv_apply hU hf
  have hda : ∀ v, DifferentiableAt ℂ (fun x => fderiv ℂ f x v) c := fun v =>
    (hd v).differentiableAt (hU.mem_nhds hc)
  let L₀ : E →ₗ[ℂ] E →L[ℂ] V :=
    { toFun := fun v => fderiv ℂ (fun x => fderiv ℂ f x v) c
      map_add' := fun v u => by
        simp only [map_add]
        exact fderiv_fun_add (hda v) (hda u)
      map_smul' := fun a v => by
        simp only [map_smul, RingHom.id_apply]
        exact fderiv_fun_const_smul (hda v) a }
  let L : E →L[ℂ] E →L[ℂ] V := L₀.mkContinuous (2 * C / r) fun v =>
    (SCV.norm_fderiv_le_of_ball hr0 ((hd v).mono hrU) (hb v)).trans_eq (by ring)
  have key : ∀ z ∈ ball c r, ‖fderiv ℂ f z - fderiv ℂ f c - L.flip (z - c)‖ ≤ 4 * C / r ^ 2 * ‖‖z - c‖ ^ 2‖ := by
    intro z hz
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    refine (SCV.norm_sub_sub_fderiv_le_of_ball ((hd v).mono hrU) (hb v) hz).trans_eq ?_
    rw [norm_pow, norm_norm]; ring
  have hF : HasFDerivAt (fderiv ℂ f) L.flip c := by
    rw [hasFDerivAt_iff_isLittleO]
    refine (Asymptotics.IsBigO.of_bound _ (mem_of_superset (ball_mem_nhds c hr0) key)).trans_isLittleO ?_
    exact Asymptotics.isLittleO_pow_sub_sub c one_lt_two
  exact hF.differentiableAt.differentiableWithinAt

theorem contDiffOn_nat {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {U : Set E} (hU : IsOpen U) (n : ℕ) :
    ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] {f : E → V},
      DifferentiableOn ℂ f U → ContDiffOn ℂ n f U := by
  induction n with
  | zero => intro V _ _ _ f hf; exact contDiffOn_zero.mpr hf.continuousOn
  | succ n ih =>
    intro V _ _ _ f hf
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hU]
    exact ⟨hf, by simp, ih (differentiableOn_fderiv hU hf)⟩

theorem contDiffAt_two_real {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E] {U : Set E} (hU : IsOpen U) {f : E → ℂ} (hf : DifferentiableOn ℂ f U) {z : E}
    (hz : z ∈ U) : ContDiffAt ℝ 2 f z :=
  ((contDiffOn_nat hU 2 hf).contDiffAt (hU.mem_nhds hz)).restrict_scalars ℝ

end GlobalTheory.HoloNormed
