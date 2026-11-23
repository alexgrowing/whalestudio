import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousFourierGau

open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder

namespace GlobalTheory.RealWeil

theorem hasFDerivAt_of_norming {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {B : Type} [NormedAddCommGroup B]
    [NormedSpace ℂ B] {X : Type} (l : X → B →L[ℂ] ℂ) (h1 : ∀ x b, ‖l x b‖ ≤ ‖b‖)
    (h2 : ∀ b (C : ℝ), 0 ≤ C → (∀ x, ‖l x b‖ ≤ C) → ‖b‖ ≤ C) (F : V → B) (A : V → V →L[ℝ] B) (hA : Continuous A)
    (hF : ∀ x v, HasFDerivAt (fun w => l x (F w)) (((l x).restrictScalars ℝ).comp (A v)) v) (v : V) :
    HasFDerivAt F (A v) v := by
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨δ, hδ, hb⟩ := Metric.continuousAt_iff.1 (hA.continuousAt (x := v)) c hc
  filter_upwards [Metric.ball_mem_nhds v hδ] with w hw
  refine h2 _ _ (by positivity) fun x => ?_
  have := (convex_ball v δ).norm_image_sub_le_of_norm_hasFDerivWithin_le' (𝕜 := ℝ) (C := c)
    (φ := ((l x).restrictScalars ℝ).comp (A v))
    (fun u _ => (hF x u).hasFDerivWithinAt) (fun u hu => ?_) (Metric.mem_ball_self hδ) hw
  · simpa only [map_sub, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars'] using this
  · refine ContinuousLinearMap.opNorm_le_bound _ hc.le fun z => ?_
    have e : (((l x).restrictScalars ℝ).comp (A u) - ((l x).restrictScalars ℝ).comp (A v)) z = l x ((A u - A v) z) := by
      simp
    rw [e]
    refine (h1 _ _).trans (((A u - A v).le_opNorm z).trans ?_)
    have := hb hu
    rw [dist_eq_norm] at this
    gcongr

theorem sm_of_weak_deriv_closed : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (om : V →L[ℝ] V →L[ℝ] ℝ)
    (ρ : V → B →L[ℂ] B), IsHeis (fun x y => om x y) ρ → ∀ (X : Type) (l : X → B →L[ℂ] ℂ), (∀ x b, ‖l x b‖ ≤ ‖b‖) →
    (∀ b (C : ℝ), 0 ≤ C → (∀ x, ‖l x b‖ ≤ C) → ‖b‖ ≤ C) →
    (∀ x v, ∃ (a : ℂ) (x' : X), ∀ b, l x (ρ v b) = a * l x' b) → ∀ Θ : Set B,
    (∀ f ∈ Θ, ∀ x, Differentiable ℝ fun v => l x (ρ v f)) →
    (∀ f ∈ Θ, ∀ z : V, ∃ f' ∈ Θ, ∀ x, HasDerivAt (fun t : ℝ => l x (ρ (t • z) f)) (l x f') 0) →
    ∀ f ∈ Θ, Sm ρ f := by
  intro V _ _ _ B _ _ _ om ρ h X l h1 h2 h3 Θ hd hc
  have sep : ∀ b b' : B, (∀ x, l x b = l x b') → b = b' := fun b b' hb => by
    rw [← sub_eq_zero, ← norm_le_zero_iff]
    exact h2 _ 0 le_rfl fun x => by rw [map_sub, hb, sub_self, norm_zero]
  have lsm : ∀ x (r : ℝ) (b : B), l x (r • b) = r • l x b := fun x r b => ((l x).restrictScalars ℝ).map_smul r b
  have key : ∀ f ∈ Θ, ∃ D : V →L[ℝ] B, (∀ z, D z ∈ Θ) ∧
      ∀ v, HasFDerivAt (fun w => ρ w f) (((ρ v).restrictScalars ℝ).comp D -
        (om v).smulRight (((π : ℂ) * I) • ρ v f)) v := by
    intro f hf
    choose g hg hg' using hc f hf
    have hgd : ∀ x z, l x (g z) = fderiv ℝ (fun v => l x (ρ v f)) 0 z := by
      intro x z
      refine (hg' z x).unique ?_
      have a1 : HasDerivAt (fun t : ℝ => t • z) z 0 := by simpa using (hasDerivAt_id (0 : ℝ)).smul_const z
      have a2 : HasFDerivAt (fun v => l x (ρ v f)) (fderiv ℝ (fun v => l x (ρ v f)) 0) ((0 : ℝ) • z) := by
        rw [zero_smul]; exact (hd f hf x 0).hasFDerivAt
      exact a2.comp_hasDerivAt (0 : ℝ) a1
    let D0 : V →ₗ[ℝ] B :=
      { toFun := g
        map_add' := fun z z' => sep _ _ fun x => by rw [map_add, hgd, hgd, hgd, map_add]
        map_smul' := fun r z => sep _ _ fun x => by rw [RingHom.id_apply, lsm, hgd, hgd, map_smul] }
    let D : V →L[ℝ] B := LinearMap.toContinuousLinearMap D0
    have hD : ∀ z, D z = g z := fun z => rfl
    refine ⟨D, fun z => hg z, hasFDerivAt_of_norming l h1 h2 _ _ ?_ ?_⟩
    · refine continuous_clm_apply.2 fun z => ?_
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.smulRight_apply]
      have a1 := h.2.2.2 (D z)
      have a2 := h.2.2.2 f
      exact a1.sub ((om.continuous.clm_apply continuous_const).smul (a2.const_smul _))
    · intro x v
      obtain ⟨a, x', hx⟩ := h3 x v
      have e : (fun w => l x (ρ w f)) =
          fun w => cexp (-(π * I) * (om v (w - v) : ℝ)) * (a * l x' (ρ (w - v) f)) := by
        funext w
        rw [← hx, h.2.1, add_sub_cancel, map_smul, smul_eq_mul, ← mul_assoc, ← Complex.exp_add]
        simp
      have b0 : HasFDerivAt (fun w : V => w - v) (ContinuousLinearMap.id ℝ V) v := (hasFDerivAt_id v).sub_const v
      have b1 : HasFDerivAt (fun w => l x' (ρ (w - v) f)) (fderiv ℝ (fun v => l x' (ρ v f)) 0) v := by
        have a2 : HasFDerivAt (fun v => l x' (ρ v f)) (fderiv ℝ (fun v => l x' (ρ v f)) 0) (v - v) := by
          rw [sub_self]; exact (hd f hf x' 0).hasFDerivAt
        simpa [Function.comp_def] using HasFDerivAt.comp (f := fun w : V => w - v) v a2 b0
      have b2 : HasFDerivAt (fun w : V => ((om v (w - v) : ℝ) : ℂ)) (Complex.ofRealCLM.comp (om v)) v := by
        simpa [Function.comp_def] using (Complex.ofRealCLM.comp (om v)).hasFDerivAt.comp v b0
      have b3 := ((b2.const_mul (-(π * I) : ℂ)).cexp).mul (b1.const_mul a)
      rw [e]
      refine b3.congr_fderiv ?_
      ext z
      simp [← hgd, h.1, hD, lsm, hx]
      ring
  have ind : ∀ n : ℕ, ∀ f ∈ Θ, ContDiff ℝ n fun v => ρ v f := by
    intro n
    induction n with
    | zero => intro f _; exact contDiff_zero.2 (h.2.2.2 f)
    | succ n ih =>
      intro f hf
      obtain ⟨D, hD, hF⟩ := key f hf
      rw [Nat.cast_succ, contDiff_succ_iff_fderiv_apply]
      refine ⟨fun v => (hF v).differentiableAt, by simp, fun z => ?_⟩
      simp only [(hF _).fderiv, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.smulRight_apply]
      exact (ih _ (hD z)).sub ((om.contDiff.clm_apply contDiff_const).smul ((ih f hf).const_smul _))
  intro f hf
  exact contDiff_infty.2 fun n => ind n f hf

end GlobalTheory.RealWeil
