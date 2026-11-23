import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSameOrdersLiftCentre
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

theorem eventually_const_mem_ball_one {r : ℝ} (hr : 0 < r) :
    ∀ᶠ τ in 𝓝 (0 : ℂ), (fun _ : Fin 1 ↦ τ) ∈ Metric.ball (0 : Fin 1 → ℂ) r := by
  have hc : Continuous (fun τ : ℂ ↦ (fun _ : Fin 1 ↦ τ)) := continuous_pi fun _ ↦ continuous_id
  exact hc.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds (0 : Fin 1 → ℂ) hr)

theorem analyticAt_comp_const_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {φ : (Fin 1 → ℂ) → E} {r : ℝ} (hr : 0 < r) (hφ : DifferentiableOn ℂ φ (Metric.ball 0 r)) :
    AnalyticAt ℂ (fun τ : ℂ ↦ φ (fun _ ↦ τ)) 0 := by
  have hc : Differentiable ℂ (fun τ : ℂ ↦ (fun _ : Fin 1 ↦ τ)) :=
    differentiable_pi.2 fun _ ↦ differentiable_id
  exact DifferentiableOn.analyticAt (s := (fun τ : ℂ ↦ (fun _ : Fin 1 ↦ τ)) ⁻¹' Metric.ball 0 r)
    (hφ.comp hc.differentiableOn fun _ h ↦ h) (eventually_const_mem_ball_one hr)

theorem analyticAt_eval_of_analyticAt_zero {n : ℕ} {F : ℂ → Fin n → ℂ} (hF : AnalyticAt ℂ F 0)
    (p : MvPolynomial (Fin n) ℂ) : AnalyticAt ℂ (fun τ ↦ eval (F τ) p) 0 := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using analyticAt_const
  | add p q hp hq => simp only [map_add]; exact hp.add hq
  | mul_X p i hp => simp only [map_mul, eval_X]; exact hp.mul (analyticAt_pi_iff.mp hF i)

theorem branchOrder_ne_top_of_not_mem (hB : BranchOffHypersurface.Statement) {n : ℕ}
    {J : Ideal (MvPolynomial (Fin n) ℂ)} {q : Fin n → ℂ} (γ : VarBranch J 1 q) (hJ : J.IsPrime)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (1 : ℕ)) {b : MvPolynomial (Fin n) ℂ} (hb : b ∉ J) :
    branchOrder γ b ≠ ⊤ := by
  intro htop
  obtain ⟨ε, hε, hεb⟩ := Metric.eventually_nhds_iff_ball.1 (analyticOrderAt_eq_top.1 htop)
  have hU : Metric.ball (0 : Fin 1 → ℂ) (min ε γ.radius) ⊆ Metric.ball 0 γ.radius :=
    Metric.ball_subset_ball (min_le_right _ _)
  obtain ⟨t, ht, hne⟩ := hB n 1 J b _ γ.toFun hJ hdim hb Metric.isOpen_ball
    ⟨0, Metric.mem_ball_self (lt_min hε γ.radius_pos)⟩ (γ.differentiableOn.mono hU) (γ.injOn.mono hU)
    fun t ht ↦ γ.mapsTo (hU ht)
  have ht0 : (fun _ : Fin 1 ↦ t 0) = t := funext fun i ↦ by rw [Subsingleton.elim i 0]
  apply hne
  rw [← ht0]
  apply hεb
  rw [Metric.mem_ball, dist_zero_right] at ht ⊢
  exact lt_of_le_of_lt (norm_le_pi_norm t 0) (lt_of_lt_of_le ht (min_le_left _ _))

theorem SameOrdersLiftCentre.proof (hB : BranchOffHypersurface.Statement) : SameOrdersLiftCentre.Statement := by
  intro n J q M γ γ' Γ Γ' hJ hdim hΓd hΓ hΓ'd hΓ' hord
  funext s
  rcases s with j | i
  · have e := congrFun (hΓ 0 (Metric.mem_ball_self γ.radius_pos)).2 j
    have e' := congrFun (hΓ' 0 (Metric.mem_ball_self γ'.radius_pos)).2 j
    simp only [firstCoords] at e e'
    rw [e, e', γ.map_zero, γ'.map_zero]
  obtain ⟨a, b, hb, hab⟩ := M.birational i

  have key : ∀ (c : VarBranch J 1 q) (L : (Fin 1 → ℂ) → Fin n ⊕ Fin M.m → ℂ),
      DifferentiableOn ℂ L (Metric.ball 0 c.radius) →
      (∀ τ ∈ Metric.ball 0 c.radius, L τ ∈ zeroSetIn M.ideal ∧ firstCoords (L τ) = c.toFun τ) → ∀ l : ℂ,
      branchOrder c (a - C l * b) =
        branchOrder c b + analyticOrderAt (fun τ : ℂ ↦ L (fun _ ↦ τ) (Sum.inr i) - l) 0 := by
    intro c L hLd hL l
    have hLa : AnalyticAt ℂ (fun τ : ℂ ↦ L (fun _ ↦ τ) (Sum.inr i) - l) 0 :=
      ((analyticAt_pi_iff.mp (analyticAt_comp_const_one c.radius_pos hLd)) (Sum.inr i)).sub analyticAt_const
    have hBa := analyticAt_eval_of_analyticAt_zero (analyticAt_comp_const_one c.radius_pos c.differentiableOn) b
    rw [branchOrder, branchOrder, ← analyticOrderAt_mul hBa hLa]
    apply analyticOrderAt_congr
    filter_upwards [eventually_const_mem_ball_one c.radius_pos] with τ hτ
    have h := (hL _ hτ).1 _ hab
    simp only [eval_sub, eval_mul, eval_X, eval_rename] at h
    change eval (firstCoords (L fun _ ↦ τ)) b * _ - eval (firstCoords (L fun _ ↦ τ)) a = 0 at h
    rw [(hL _ hτ).2] at h
    simp only [eval_sub, eval_mul, eval_C, Pi.mul_apply]
    linear_combination -h
  set l := Γ 0 (Sum.inr i)
  have k1 := key γ Γ hΓd hΓ l
  have k2 := key γ' Γ' hΓ'd hΓ' l
  rw [← hord, ← hord] at k2
  have heq := WithTop.add_left_cancel (branchOrder_ne_top_of_not_mem hB γ hJ hdim hb) (k1.symm.trans k2)
  have hGa : AnalyticAt ℂ (fun τ : ℂ ↦ Γ (fun _ ↦ τ) (Sum.inr i) - l) 0 :=
    ((analyticAt_pi_iff.mp (analyticAt_comp_const_one γ.radius_pos hΓd)) (Sum.inr i)).sub analyticAt_const
  have hG'a : AnalyticAt ℂ (fun τ : ℂ ↦ Γ' (fun _ ↦ τ) (Sum.inr i) - l) 0 :=
    ((analyticAt_pi_iff.mp (analyticAt_comp_const_one γ'.radius_pos hΓ'd)) (Sum.inr i)).sub analyticAt_const
  have hz : analyticOrderAt (fun τ : ℂ ↦ Γ (fun _ ↦ τ) (Sum.inr i) - l) 0 ≠ 0 :=
    hGa.analyticOrderAt_ne_zero.2 (sub_self _)
  rw [heq] at hz
  exact (sub_eq_zero.1 (hG'a.analyticOrderAt_ne_zero.1 hz)).symm

end GroundTheory.Heights₂.Heights
