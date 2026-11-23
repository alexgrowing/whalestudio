import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FunJetApply
open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

noncomputable section

namespace GlobalTheory.SphJet.Taylor

variable {n : ℕ}

theorem analyticAt_Rz {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
    {f : Matrix (Fin n) (Fin n) ℂ → B} (hf : AnalyticAt ℂ f 1) (Z : Matrix (Fin n) (Fin n) ℂ) :
    AnalyticAt ℂ (Rz Z f) 1 := by
  unfold Rz
  exact (ContinuousLinearMap.id ℂ (Matrix (Fin n) (Fin n) ℂ →L[ℂ] B)).analyticAt_bilinear _ |>.comp₂ hf.fderiv
    (analyticAt_id.mul analyticAt_const)

theorem analyticAt_Rw {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (ε : Fin n → Bool)
    {f : Matrix (Fin n) (Fin n) ℂ → B} (hf : AnalyticAt ℂ f 1) (l : List (Fin n × Fin n)) :
    AnalyticAt ℂ (Rw ε l f) 1 := by
  induction l with
  | nil => exact hf
  | cons p l ih => exact analyticAt_Rz ih _

theorem hasDerivAt_expC (Z : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) :
    HasDerivAt (fun t : ℂ => NormedSpace.exp (t • Z)) (NormedSpace.exp (s • Z) * Z) s :=
  hasDerivAt_exp_smul_const Z s

theorem analyticAt_expC (Z : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) :
    AnalyticAt ℂ (fun t : ℂ => NormedSpace.exp (t • Z)) s :=
  Differentiable.analyticAt (fun t => (hasDerivAt_expC Z t).differentiableAt) s

theorem analyticAt_comp {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]
    {g : Matrix (Fin n) (Fin n) ℂ → B} (hg : AnalyticAt ℂ g 1) (L : B →L[ℂ] ℂ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    AnalyticAt ℝ (fun t : ℝ => L (g (NormedSpace.exp ((t : ℂ) • Z)))) 0 := by
  have h1 : AnalyticAt ℂ (fun t : ℂ => L (g (NormedSpace.exp (t • Z)))) 0 :=
    (L.analyticAt _).comp (AnalyticAt.comp_of_eq hg (analyticAt_expC Z 0) (by simp))
  have h2 := AnalyticAt.comp_of_eq (h1.restrictScalars (𝕜 := ℝ)) (Complex.ofRealCLM.analyticAt 0) (by simp)
  exact h2

theorem deriv_comp_eventually {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
    {g : Matrix (Fin n) (Fin n) ℂ → B} (hg : AnalyticAt ℂ g 1) (L : B →L[ℂ] ℂ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    deriv (fun t : ℝ => L (g (NormedSpace.exp ((t : ℂ) • Z)))) =ᶠ[𝓝 0]
      fun t : ℝ => L (Rz Z g (NormedSpace.exp ((t : ℂ) • Z))) := by
  have hc : Tendsto (fun t : ℝ => NormedSpace.exp ((t : ℂ) • Z)) (𝓝 0) (𝓝 1) := by
    have : ContinuousAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • Z)) 0 :=
      (hasDerivAt_expC Z ((0 : ℝ) : ℂ)).continuousAt.comp Complex.continuous_ofReal.continuousAt
    simpa [ContinuousAt] using this
  filter_upwards [hc.eventually hg.eventually_analyticAt] with t ht
  have h1 : HasDerivAt (fun s : ℂ => L (g (NormedSpace.exp (s • Z))))
      (L (Rz Z g (NormedSpace.exp ((t : ℂ) • Z)))) (t : ℂ) :=
    L.hasFDerivAt.comp_hasDerivAt _ (ht.differentiableAt.hasFDerivAt.comp_hasDerivAt _ (hasDerivAt_expC Z t))
  exact h1.comp_ofReal.deriv

theorem Rz_thM {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] (ε : Fin n → Bool)
    (X : Matrix (Fin n) (Fin n) ℂ) (g : Matrix (Fin n) (Fin n) ℂ → B) (z : Matrix (Fin n) (Fin n) ℂ) :
    Rz (thM ε X) g z = ∑ p : Fin n × Fin n, X p.1 p.2 • Rz (thE ε p) g z := by
  simp only [Rz, thM, Finset.mul_sum, map_sum, mul_smul_comm, map_smul]

theorem iteratedDeriv_inner_exp : ∀ (V W : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) [CompleteSpace W] (j : W →ₗᵢ[ℂ] V) (f : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)), AnalyticAt ℂ f 1 → (∀ l, funJet ε f l = modJet E j l) → ∀ (X : Matrix (Fin n) (Fin n) ℂ) (m : ℕ) (y x : W), iteratedDeriv m (fun t : ℝ => ⟪y, f (NormedSpace.exp ((t : ℂ) • thM ε X)) x⟫_ℂ) 0 = ⟪j y, (actM E X ^ m) (j x)⟫_ℂ := by
  intro V W _ _ _ _ n ε E _ j f hf hJ X m y x
  let L : (W →L[ℂ] W) →L[ℂ] ℂ := (innerSL ℂ y).comp (ContinuousLinearMap.apply ℂ W x)
  have hL : ∀ T : W →L[ℂ] W, L T = ⟪y, T x⟫_ℂ := fun T => rfl
  have key : ∀ (m : ℕ) (l : List (Fin n × Fin n)),
      iteratedDeriv m (fun t : ℝ => L (Rw ε l f (NormedSpace.exp ((t : ℂ) • thM ε X)))) 0 =
        ⟪j y, (actM E X ^ m) (ew E l (j x))⟫_ℂ := by
    intro m
    induction m with
    | zero =>
      intro l
      have := congrArg (fun B => B y x) (hJ l)
      simp only [funJet_apply, modJet_apply] at this
      simpa [hL] using this
    | succ m ih =>
      intro l
      rw [iteratedDeriv_succ', (deriv_comp_eventually (analyticAt_Rw ε hf l) L _).iteratedDeriv_eq]
      have e : (fun t : ℝ => L (Rz (thM ε X) (Rw ε l f) (NormedSpace.exp ((t : ℂ) • thM ε X)))) =
          fun t : ℝ => ∑ p : Fin n × Fin n,
            X p.1 p.2 * L (Rw ε (p :: l) f (NormedSpace.exp ((t : ℂ) • thM ε X))) := by
        funext t
        rw [Rz_thM, map_sum]
        simp only [map_smul, smul_eq_mul]
        rfl
      rw [e, iteratedDeriv_fun_sum (fun p _ =>
        contDiffAt_const.mul (analyticAt_comp (analyticAt_Rw ε hf (p :: l)) L _).contDiffAt)]
      have e2 : ∀ p : Fin n × Fin n, iteratedDeriv m (fun t : ℝ =>
            X p.1 p.2 * L (Rw ε (p :: l) f (NormedSpace.exp ((t : ℂ) • thM ε X)))) 0 =
          X p.1 p.2 * ⟪j y, (actM E X ^ m) (E p.1 p.2 (ew E l (j x)))⟫_ℂ := by
        intro p
        rw [iteratedDeriv_const_mul _ (analyticAt_comp (analyticAt_Rw ε hf (p :: l)) L _).contDiffAt, ih]
        simp [ew]
      simp only [e2]
      rw [pow_succ, Module.End.mul_apply]
      have e3 : ∀ v : V, actM E X v = ∑ p : Fin n × Fin n, X p.1 p.2 • E p.1 p.2 v := by
        intro v
        simp [actM, Fintype.sum_prod_type, LinearMap.sum_apply]
      rw [e3, map_sum, inner_sum]
      simp only [map_smul, inner_smul_right]
  simpa [hL, Rw, ew] using key m []

end GlobalTheory.SphJet.Taylor
