import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteFibreCentredEquation
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteFibreGermIntegral
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGermWeierstrassPreparation
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Polynomial

noncomputable def FiniteFibreCentredEquation.centredPoly (a : ℂ) {k : ℕ} (c : Fin k → ℂ) : ℂ[X] :=
  (X - C a) ^ k + ∑ j : Fin k, C (c j) * (X - C a) ^ (j : ℕ)

theorem FiniteFibreCentredEquation.centredPoly_eval (a : ℂ) {k : ℕ} (c : Fin k → ℂ) (T : ℂ) :
    (FiniteFibreCentredEquation.centredPoly a c).eval T = (T - a) ^ k + ∑ j, c j * (T - a) ^ (j : ℕ) := by
  simp [FiniteFibreCentredEquation.centredPoly, eval_finsetSum]

theorem FiniteFibreCentredEquation.centredPoly_coeff (a : ℂ) {k : ℕ} (c : Fin k → ℂ) (m : ℕ) :
    (FiniteFibreCentredEquation.centredPoly a c).coeff m =
      ((X - C a) ^ k).coeff m + ∑ j : Fin k, c j * ((X - C a) ^ (j : ℕ)).coeff m := by
  simp [FiniteFibreCentredEquation.centredPoly, finsetSum_coeff, coeff_C_mul]

theorem FiniteFibreCentredEquation.centredPoly_natDegree_lt (a : ℂ) {k : ℕ} (c : Fin k → ℂ) :
    (FiniteFibreCentredEquation.centredPoly a c).natDegree < k + 1 := by
  refine Nat.lt_succ_of_le (natDegree_add_le_of_degree_le ?_ ?_)
  · rw [(monic_X_sub_C a).natDegree_pow, natDegree_X_sub_C, mul_one]
  · refine natDegree_sum_le_of_forall_le _ _ fun j _ => (natDegree_C_mul_le _ _).trans ?_
    rw [(monic_X_sub_C a).natDegree_pow, natDegree_X_sub_C, mul_one]
    exact j.isLt.le

theorem FiniteFibreCentredEquation.centredPoly_coeff_top (a : ℂ) {k : ℕ} (c : Fin k → ℂ) : (FiniteFibreCentredEquation.centredPoly a c).coeff k = 1 := by
  rw [FiniteFibreCentredEquation.centredPoly_coeff]
  have h1 : ((X - C a) ^ k).coeff k = 1 := by
    have h := ((monic_X_sub_C a).pow k).coeff_natDegree
    rwa [(monic_X_sub_C a).natDegree_pow, natDegree_X_sub_C, mul_one] at h
  have h2 : ∀ j : Fin k, ((X - C a) ^ (j : ℕ)).coeff k = 0 := fun j =>
    coeff_eq_zero_of_natDegree_lt (by
      rw [(monic_X_sub_C a).natDegree_pow, natDegree_X_sub_C, mul_one]; exact j.isLt)
  simp [h1, h2]

theorem FiniteFibreCentredEquation.centredPoly_eval_expand (a : ℂ) {k : ℕ} (c : Fin k → ℂ) (T : ℂ) :
    (FiniteFibreCentredEquation.centredPoly a c).eval T = T ^ k + ∑ m : Fin k, (FiniteFibreCentredEquation.centredPoly a c).coeff m * T ^ (m : ℕ) := by
  rw [eval_eq_sum_range' (FiniteFibreCentredEquation.centredPoly_natDegree_lt a c), Finset.sum_range_succ, FiniteFibreCentredEquation.centredPoly_coeff_top,
    Finset.sum_range (fun m => (FiniteFibreCentredEquation.centredPoly a c).coeff m * T ^ m)]
  ring

theorem FiniteFibreCentredEquation.proof (hI : FiniteFibreGermIntegral.Statement)
    (hW : WeierstrassPreparation.Statement) : FiniteFibreCentredEquation.Statement := by
  intro σ _ S w d A hS hfib g hg
  obtain ⟨N, a, ha, hrel⟩ := hI σ S w d A hS hfib (fun z => g z - g w) (hg.sub analyticAt_const)
  set f : (Option (Fin d) → ℂ) → ℂ := fun x =>
    x none ^ N + ∑ j, a j (A w + fun i => x (some i)) * x none ^ (j : ℕ) with hf_def
  have hlast : AnalyticAt ℂ (fun x : Option (Fin d) → ℂ => x none) 0 :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Option (Fin d) => ℂ) none).analyticAt 0
  have hfirst : AnalyticAt ℂ (fun x : Option (Fin d) → ℂ => A w + fun i => x (some i)) 0 :=
    analyticAt_const.add ((ContinuousLinearMap.pi fun i : Fin d =>
      ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Option (Fin d) => ℂ) (some i)).analyticAt 0)
  have hfan : AnalyticAt ℂ f 0 := by
    refine (hlast.pow N).add (Finset.analyticAt_fun_sum _ fun j _ => ?_)
    exact ((ha j).comp_of_eq hfirst (show A w + (0 : Fin d → ℂ) = A w from add_zero _)).mul (hlast.pow _)

  set p : ℂ[X] := X ^ N + ∑ j : Fin N, C (a j (A w)) * X ^ (j : ℕ) with hp_def
  have hpm : p.Monic := monic_X_pow_add (degree_sum_fin_lt _)
  have hpe : (fun t => f (pointWithLast 0 t)) = fun t => p.eval t := by
    funext t
    have h0 : (fun i => pointWithLast (0 : Fin d → ℂ) t (some i)) = 0 := rfl
    simp only [hf_def, hp_def, h0, add_zero, eval_add, eval_pow, eval_X, eval_finsetSum, eval_mul, eval_C]
    rfl
  have hne : analyticOrderAt (fun t => f (pointWithLast 0 t)) 0 ≠ ⊤ := by
    rw [hpe]
    intro htop
    have hpan : AnalyticOnNhd ℂ (fun t => p.eval t) Set.univ := fun t _ =>
      (Polynomial.differentiable p).analyticAt t
    have hall : Set.EqOn (fun t => p.eval t) 0 Set.univ :=
      hpan.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ 0) (analyticOrderAt_eq_top.1 htop)
    exact hpm.ne_zero (Polynomial.funext fun t => by simpa using hall (Set.mem_univ t))
  obtain ⟨k, hk⟩ : ∃ k : ℕ, analyticOrderAt (fun t => f (pointWithLast 0 t)) 0 = k :=
    ⟨_, (Nat.cast_analyticOrderNatAt hne).symm⟩
  obtain ⟨e, c, he, he0, hc, hc0, hfe⟩ := hW (Fin d) k f hfan hk
  refine ⟨k, fun m y => (FiniteFibreCentredEquation.centredPoly (g w) fun j => c j (y - A w)).coeff m, fun m => ?_, fun T => ?_, ?_⟩
  · simp only [FiniteFibreCentredEquation.centredPoly_coeff]
    refine analyticAt_const.add (Finset.analyticAt_fun_sum _ fun j _ => ?_)
    exact ((hc j).comp_of_eq (f := fun y : Fin d → ℂ => y - A w) (analyticAt_id.sub analyticAt_const)
      (sub_self _)).mul analyticAt_const
  · rw [← FiniteFibreCentredEquation.centredPoly_eval_expand, FiniteFibreCentredEquation.centredPoly_eval]
    simp [hc0]
  ·
    set φ : (σ → ℂ) → (Option (Fin d) → ℂ) := fun z => pointWithLast (A z - A w) (g z - g w) with hφ_def
    have hφc : ContinuousAt φ w := by
      refine continuousAt_pi.2 fun o => ?_
      cases o with
      | none => exact hg.continuousAt.sub continuousAt_const
      | some i => exact ((continuous_apply i).comp A.continuous).continuousAt.sub continuousAt_const
    have hφw : φ w = 0 := by
      funext o; cases o <;> simp [hφ_def, pointWithLast]
    have hφt : Tendsto φ (𝓝 w) (𝓝 0) := hφw ▸ hφc.tendsto
    filter_upwards [hφt.eventually hfe, hφt.eventually (he.continuousAt.eventually_ne he0), hrel]
      with z h1 h2 h3 hzX
    have hf0 : f (φ z) = 0 := by
      show (g z - g w) ^ N + ∑ j, a j (A w + (A z - A w)) * (g z - g w) ^ (j : ℕ) = 0
      rw [add_sub_cancel]
      exact h3 hzX
    have hω : (g z - g w) ^ k + ∑ j, c j (A z - A w) * (g z - g w) ^ (j : ℕ) = 0 := by
      rw [hf0] at h1
      exact (mul_eq_zero.1 h1.symm).resolve_left h2
    rw [← FiniteFibreCentredEquation.centredPoly_eval_expand, FiniteFibreCentredEquation.centredPoly_eval]
    exact hω

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
