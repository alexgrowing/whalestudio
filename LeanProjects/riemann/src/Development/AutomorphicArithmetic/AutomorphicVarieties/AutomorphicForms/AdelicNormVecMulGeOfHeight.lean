import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelHeights.SiegelHeight
open NumberField Matrix GlobalTheory.CuspRep GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V UpperTheory.V.Fb

private theorem back_eq {E : Type*} [NormedField E] {n : ℕ} (g : GL (Fin n) E) (z : Fin n → E) :
    z = (z ᵥ* (g : Matrix (Fin n) (Fin n) E)) ᵥ* ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) := by
  rw [vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, vecMul_one]

private theorem fin_bound {E : Type*} [NormedField E] [IsUltrametricDist E] {n : ℕ}
    (g : GL (Fin n) E) (z : Fin n → E) :
    ‖z‖ ≤ locHeight g * ‖z ᵥ* (g : Matrix (Fin n) (Fin n) E)‖ := by
  have hp := locHeight_pos g
  set y := z ᵥ* (g : Matrix (Fin n) (Fin n) E) with hy
  have h0 : 0 ≤ locHeight g * ‖y‖ := by positivity
  have hz := back_eq g z
  rw [← hy] at hz
  rw [hz]
  refine (pi_norm_le_iff_of_nonneg h0).2 fun j => ?_
  simp only [vecMul, dotProduct]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg h0 fun i _ => ?_
  rw [norm_mul, mul_comm]
  exact mul_le_mul (norm_inv_apply_le_locHeight g i j) (norm_le_pi_norm y i) (norm_nonneg _) hp.le

private theorem inf_bound {E : Type*} [NormedField E] {n : ℕ}
    (g : GL (Fin n) E) (z : Fin n → E) :
    Reduction.euclidNorm z ≤ (√n * n + 1) * locHeight g *
      Reduction.euclidNorm (z ᵥ* (g : Matrix (Fin n) (Fin n) E)) := by
  have hp := locHeight_pos g
  set y := z ᵥ* (g : Matrix (Fin n) (Fin n) E) with hy
  have he := Reduction.euclidNorm_nonneg y
  have h0 : 0 ≤ (n : ℝ) * (locHeight g * Reduction.euclidNorm y) := by positivity
  have hz := back_eq g z
  rw [← hy] at hz
  have h1 : ‖z‖ ≤ (n : ℝ) * (locHeight g * Reduction.euclidNorm y) := by
    rw [hz]
    refine (pi_norm_le_iff_of_nonneg h0).2 fun j => ?_
    simp only [vecMul, dotProduct]
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum (g := fun _ => locHeight g * Reduction.euclidNorm y)
      fun i _ => ?_).trans (by simp)
    rw [norm_mul, mul_comm]
    exact mul_le_mul (norm_inv_apply_le_locHeight g i j) (Reduction.norm_le_euclidNorm y i)
      (norm_nonneg _) hp.le
  calc Reduction.euclidNorm z ≤ √n * ‖z‖ := Reduction.euclidNorm_le_sqrt_mul z
    _ ≤ √n * ((n : ℝ) * (locHeight g * Reduction.euclidNorm y)) :=
        mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)
    _ = (√n * n) * (locHeight g * Reduction.euclidNorm y) := by ring
    _ ≤ (√n * n + 1) * (locHeight g * Reduction.euclidNorm y) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = _ := by ring

private theorem finprod_bound {ι : Type*} {a b c : ι → ℝ} (ha : (Function.mulSupport a).Finite)
    (hb : (Function.mulSupport b).Finite) (hc : (Function.mulSupport c).Finite)
    (h0 : ∀ i, 0 ≤ a i) (h : ∀ i, a i ≤ b i * c i) :
    ∏ᶠ i, a i ≤ (∏ᶠ i, b i) * ∏ᶠ i, c i := by
  classical
  rw [finprod_eq_prod_of_mulSupport_subset a (s := ((ha.union hb).union hc).toFinset)
      (fun v hv => by simp only [Set.Finite.coe_toFinset]; exact Or.inl (Or.inl hv)),
    finprod_eq_prod_of_mulSupport_subset b (s := ((ha.union hb).union hc).toFinset)
      (fun v hv => by simp only [Set.Finite.coe_toFinset]; exact Or.inl (Or.inr hv)),
    finprod_eq_prod_of_mulSupport_subset c (s := ((ha.union hb).union hc).toFinset)
      (fun v hv => by simp only [Set.Finite.coe_toFinset]; exact Or.inr hv),
    ← Finset.prod_mul_distrib]
  exact Finset.prod_le_prod (fun i _ => h0 i) fun i _ => h i

private theorem combine {A B C P Q R S : ℝ} (hi : A ≤ C * P * Q) (hf : B ≤ R * S) (hA : 0 ≤ A)
    (hB : 0 ≤ B) : A * B ≤ C * (P * R) * (Q * S) :=
  (mul_le_mul hi hf hB (hA.trans hi)).trans (le_of_eq (by ring))

private theorem adelic_bound {K : Type} [Field K] [NumberField K] {n : ℕ}
    (g : AdelicGLn.AdelicGL K n) {y : Fin n → AdeleRing (𝓞 K) K}
    (hy : Reduction.HasFiniteContent y) :
    Reduction.adelicNorm y ≤ (∏ w : InfinitePlace K, (√n * n + 1 : ℝ) ^ w.mult) *
      AutomorphicForm.height g * Reduction.adelicNorm (y ᵥ* g.val) := by
  refine combine ?_ ?_
    (Finset.prod_nonneg fun _ _ => pow_nonneg (Reduction.euclidNorm_nonneg _) _)
    (finprod_nonneg fun _ => norm_nonneg _)
  · rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod (fun w _ => pow_nonneg (Reduction.euclidNorm_nonneg _) _)
      fun w _ => ?_
    rw [← mul_pow, ← mul_pow, Reduction.infComp_vecMul_GL]
    exact pow_le_pow_left₀ (Reduction.euclidNorm_nonneg _) (inf_bound _ _) _
  · refine finprod_bound hy.finite_mulSupport (finite_mulSupport_locHeight_finAt g)
      (hy.vecMul g).finite_mulSupport (fun _ => norm_nonneg _) fun v => ?_
    rw [Reduction.finComp_vecMul_GL]
    exact fin_bound _ _

theorem UpperTheory.adelicNorm_vecMul_ge_of_height :
    UpperTheory.V.Fb.VecLower := by
  intro K _ _ n
  refine ⟨∏ w : InfinitePlace K, (√n * n + 1 : ℝ) ^ w.mult, 1,
    Finset.prod_pos fun w _ => by positivity, fun g x hx => ?_⟩
  rw [pow_one]
  exact (Reduction.one_le_adelicNorm_ratVec hx).trans
    (adelic_bound g (Reduction.hasFiniteContent_ratVec hx))
