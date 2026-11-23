import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.WhittakerSmoothForms.Smooth

noncomputable section

open Set Filter Topology

namespace PositivityTheory.KB.WhittakerCocycle

set_option linter.unusedSectionVars false

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {Γ : Type} [Group Γ]

variable (U : Set V) (A : Γ →* (V →L[ℝ] V)) (φ : V → ℝ)

theorem extDeriv_delG (n : ℕ) {q : ℕ} (β : (ℕ → Γ) → V → V [⋀^Fin q]→L[ℝ] ℝ) (σ : ℕ → Γ) (h : V)
    (hd : ∀ i, DifferentiableAt ℝ (β (skip i σ)) h) :
    delG n (fun τ => extDeriv (β τ)) σ h = extDeriv (delG n β σ) h := by
  have e : delG n β σ = fun x => ∑ i ∈ Finset.range (n + 2), (-1 : ℝ) ^ i • β (skip i σ) x := by
    funext x; simp [delG, Finset.sum_apply]
  rw [e, extDeriv, fderiv_fun_sum (A := fun i y => (-1 : ℝ) ^ i • β (skip i σ) y)
    (fun i _ => (hd i).const_smul ((-1 : ℝ) ^ i))]
  simp only [fderiv_fun_const_smul (hd _), delG, Finset.sum_apply, Pi.smul_apply, extDeriv,
    ← ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply, map_sum, map_smul]

theorem pCoc (hH : PHom U A φ) (hS : PSmooth U A φ) (hC : PClosed U A φ) :
    PCoc U A φ := by
  intro H k c hc j
  induction j with
  | zero =>
    intro _ σ h _
    ext v
    simp only [delG, Finset.sum_apply, Pi.smul_apply, eta_zero, ContinuousAlternatingMap.sum_apply,
      ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.constOfIsEmpty_apply,
      ContinuousAlternatingMap.coe_zero, Pi.zero_apply, smul_eq_mul, Nat.sub_zero]
    rw [Finset.sum_range]
    refine (Finset.sum_congr rfl fun i _ => ?_).trans (hc.coc fun l => σ l)
    congr 2
    funext l
    exact skip_succAbove σ i l
  | succ j ih =>
    intro hj σ h hh
    have hj' : j ≤ k + 1 := by omega
    have e1 : k + 1 - (j + 1) = k - j := by omega
    rw [e1]
    have e2 : delG (k - j) (eta A φ c (j + 1)) σ h =
        delG (k - j) (fun τ => extDeriv (Kf A φ (eta A φ c j) τ)) σ h := rfl
    rw [e2, extDeriv_delG (k - j) (Kf A φ (eta A φ c j)) σ h (fun i =>
      ((hS H k c j _).2.contDiffAt (H.isOpen.mem_nhds hh)).differentiableAt (by simp))]
    have hev : delG (k - j) (Kf A φ (eta A φ c j)) σ =ᶠ[𝓝 h] eta A φ c j σ := by
      filter_upwards [H.isOpen.mem_nhds hh] with x hx
      rw [hH H j (k - j) (eta A φ c j) σ x hx]
      have h0 : Kf A φ (delG (k - j + 1) (eta A φ c j)) σ x = 0 := by
        unfold Kf
        have e3 : k - j + 1 = k + 1 - j := by omega
        simp only [e3, ih hj' _ x hx, smul_zero, finsum_zero]
      rw [h0, sub_zero]
    rw [hev.extDeriv_eq]
    exact hC H k c j σ h hh

end PositivityTheory.KB.WhittakerCocycle

end
