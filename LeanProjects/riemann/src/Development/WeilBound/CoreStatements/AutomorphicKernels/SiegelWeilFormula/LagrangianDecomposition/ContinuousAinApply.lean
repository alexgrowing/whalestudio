import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.NormIteratedFDerivBLe

noncomputable section

open scoped ContDiff LineDeriv
open MeasureTheory Set Filter Topology

namespace PositivityTheory.SiegelWeilFormula.Ald.PCI

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {κ' κ'' : Type} [Fintype κ']
  [Fintype κ'']

def inr2 : (κ'' → W) →L[ℝ] (κ' ⊕ κ'' → W) := LinearMap.toContinuousLinearMap
  { toFun := fun v => Sum.elim (0 : κ' → W) v
    map_add' := fun v w => by funext j; rcases j with j | j <;> simp
    map_smul' := fun c v => by funext j; rcases j with j | j <;> simp }

theorem inr_two_apply (v : κ'' → W) : (inr2 v : κ' ⊕ κ'' → W) = Sum.elim (0 : κ' → W) v := rfl

theorem Ain_eq (s : ℝ) (x : κ' ⊕ κ'' → W) : Ain s x = Ain 0 x + s • inr2 (x ∘ Sum.inr) := by
  funext j; rcases j with j | j <;> simp [Ain_apply, sc, inr_two_apply]

theorem Ain_one (x : κ' ⊕ κ'' → W) : Ain 1 x = x := by
  funext j; rcases j with j | j <;> simp [Ain_apply, sc]

theorem Ain_zero_inr (x : κ' ⊕ κ'' → W) : Ain 0 x ∘ Sum.inr = (0 : κ'' → W) := by
  funext j; simp [Ain_apply, sc]

theorem eq_integral (f : SchwartzMap (κ' ⊕ κ'' → W) ℂ) (hf : ∀ x : κ' ⊕ κ'' → W, x ∘ Sum.inr = 0 → f x = 0)
    (x : κ' ⊕ κ'' → W) : f x = ∫ s in Ioc (0 : ℝ) 1, fderiv ℝ f (Ain s x) (inr2 (x ∘ Sum.inr)) := by
  have hd : ∀ s : ℝ, HasDerivAt (fun s => f (Ain s x)) (fderiv ℝ f (Ain s x) (inr2 (x ∘ Sum.inr))) s := by
    intro s
    have hγ : HasDerivAt (fun s : ℝ => Ain 0 x + s • inr2 (x ∘ Sum.inr)) (inr2 (x ∘ Sum.inr)) s := by
      simpa using ((hasDerivAt_id s).smul_const (inr2 (x ∘ Sum.inr) : κ' ⊕ κ'' → W)).const_add (Ain 0 x)
    have hγ' : HasDerivAt (fun s : ℝ => Ain s x) (inr2 (x ∘ Sum.inr)) s := by
      rw [show (fun s : ℝ => Ain s x) = fun s : ℝ => Ain 0 x + s • inr2 (x ∘ Sum.inr) from funext fun s => Ain_eq s x]
      exact hγ
    exact (f.differentiableAt (x := Ain s x)).hasFDerivAt.comp_hasDerivAt_of_eq s hγ' rfl
  have hc : Continuous fun s : ℝ => fderiv ℝ f (Ain s x) (inr2 (x ∘ Sum.inr)) := by
    have h1 : Continuous fun s : ℝ => Ain s x := by
      rw [show (fun s : ℝ => Ain s x) = fun s : ℝ => Ain 0 x + s • inr2 (x ∘ Sum.inr) from funext fun s => Ain_eq s x]
      exact continuous_const.add (continuous_id.smul continuous_const)
    exact ((f.smooth ⊤).continuous_fderiv (by simp)).comp h1 |>.clm_apply continuous_const
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := 1) (fun s _ => hd s)
    (hc.intervalIntegrable _ _)
  rw [Ain_one, hf _ (Ain_zero_inr x), sub_zero, intervalIntegral.integral_of_le zero_le_one] at h
  exact h.symm

theorem continuous_Ain_apply (x : κ' ⊕ κ'' → W) : Continuous fun s : ℝ => Ain s x := by
  rw [show (fun s : ℝ => Ain s x) = fun s : ℝ => Ain 0 x + s • inr2 (x ∘ Sum.inr) from funext fun s => Ain_eq s x]
  exact continuous_const.add (continuous_id.smul continuous_const)

theorem param_hadamard (f : SchwartzMap (κ' ⊕ κ'' → W) ℂ) (hf : ∀ x : κ' ⊕ κ'' → W, x ∘ Sum.inr = 0 → f x = 0) :
    ∃ (n : ℕ) (L : Fin n → (κ'' → W) →L[ℝ] ℝ) (hh gg : Fin n → SchwartzMap (κ' ⊕ κ'' → W) ℂ),
      (∀ i x, gg i x = (L i (x ∘ Sum.inr) : ℂ) * hh i x) ∧ ∀ x, f x = ∑ i, gg i x := by
  let b := Module.finBasis ℝ (κ'' → W)
  let L : Fin (Module.finrank ℝ (κ'' → W)) → (κ'' → W) →L[ℝ] ℝ := fun i =>
    LinearMap.toContinuousLinearMap (b.coord i)
  have hL : ∀ i v, L i v = b.repr v i := fun i v => by simp [L, Module.Basis.coord_apply]
  let q : (κ'' → W) → ℝ := fun v => ∑ i, L i v ^ 2
  have hq : q.HasTemperateGrowth := by
    simp only [q]
    exact Function.HasTemperateGrowth.sum fun i _ => ((L i).hasTemperateGrowth).pow 2
  let β : (κ'' → W) → ℝ := fun v => 1 - q v * GlobalTheory.SchwartzDiv.invCut (q v)
  have hβs : ContDiff ℝ ∞ β := contDiff_const.sub (hq.1.mul (GlobalTheory.SchwartzDiv.contDiff_invCut.comp hq.1))
  have hβ0 : ∀ v, 1 ≤ q v → β v = 0 := by
    intro v hv
    simp only [β]
    rw [GlobalTheory.SchwartzDiv.invCut_of_one_le hv, mul_inv_cancel₀ (by linarith), sub_self]
  have hnorm : ∀ v, q v < 1 → ‖v‖ ≤ ∑ i, ‖b i‖ := by
    intro v hv
    have hLi : ∀ i, |L i v| ≤ 1 := by
      intro i
      have : L i v ^ 2 ≤ q v :=
        Finset.single_le_sum (f := fun j => L j v ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
      exact (sq_le_one_iff_abs_le_one _).1 (by linarith)
    calc ‖v‖ = ‖∑ i, L i v • b i‖ := by simp only [hL, b.sum_repr]
      _ ≤ ∑ i, ‖L i v • b i‖ := norm_sum_le _ _
      _ ≤ ∑ i, ‖b i‖ := Finset.sum_le_sum fun i _ => by
        rw [norm_smul, Real.norm_eq_abs]; exact mul_le_of_le_one_left (norm_nonneg _) (hLi i)
  have hβc : HasCompactSupport β := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : κ'' → W) (∑ i, ‖b i‖)) fun v hv => ?_
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hv
    have : 1 ≤ q v := by
      by_contra h
      exact absurd (hnorm v (not_le.1 h)) (not_le.2 hv)
    exact hβ0 v this
  let d : Fin (Module.finrank ℝ (κ'' → W)) → SchwartzMap (κ' ⊕ κ'' → W) ℂ := fun i => ∂_{(inr2 (κ' := κ') (b i) : κ' ⊕ κ'' → W)} f
  have hdi : ∀ i y, d i y = fderiv ℝ f y (inr2 (b i)) := fun i y => SchwartzMap.lineDerivOp_apply_eq_fderiv _ _ _
  have key : ∀ x, f x = ∑ i, (L i (x ∘ Sum.inr) : ℂ) * ∫ s in Ioc (0 : ℝ) 1, d i (Ain s x) := by
    intro x
    rw [eq_integral f hf x]
    have e1 : ∀ s : ℝ, fderiv ℝ f (Ain s x) (inr2 (x ∘ Sum.inr)) =
        ∑ i, (L i (x ∘ Sum.inr) : ℂ) * d i (Ain s x) := by
      intro s
      rw [show (inr2 (x ∘ Sum.inr) : κ' ⊕ κ'' → W) = inr2 (∑ i, b.repr (x ∘ Sum.inr) i • b i) by rw [b.sum_repr],
        map_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, map_smul, Complex.real_smul, hdi, hL]
    simp_rw [e1]
    rw [integral_finset_sum]
    · exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
    · intro i _
      exact (continuous_const.mul ((d i).continuous.comp (continuous_Ain_apply x))).integrableOn_Ioc
  choose N hN using fun i => near_schwartz (d i) β hβs hβc
  let a : Fin (Module.finrank ℝ (κ'' → W)) → (κ' ⊕ κ'' → W) → ℂ := fun i x =>
    ((L i (x ∘ Sum.inr) * GlobalTheory.SchwartzDiv.invCut (q (x ∘ Sum.inr)) : ℝ) : ℂ)
  have hr : (fun x : κ' ⊕ κ'' → W => x ∘ Sum.inr).HasTemperateGrowth :=
    (GlobalTheory.SchwartzBox.restr W (Sum.inr : κ'' → κ' ⊕ κ'')).hasTemperateGrowth
  have ha : ∀ i, (a i).HasTemperateGrowth := fun i =>
    Function.Complex.hasTemperateGrowth_ofReal.comp
      (((L i).hasTemperateGrowth.mul (GlobalTheory.SchwartzDiv.hasTemperateGrowth_invCut.comp hq)).comp hr)
  have hLc : ∀ i, (fun x : κ' ⊕ κ'' → W => (L i (x ∘ Sum.inr) : ℂ)).HasTemperateGrowth := fun i =>
    Function.Complex.hasTemperateGrowth_ofReal.comp ((L i).hasTemperateGrowth.comp hr)
  let hh : Fin (Module.finrank ℝ (κ'' → W)) → SchwartzMap (κ' ⊕ κ'' → W) ℂ := fun i =>
    N i + SchwartzMap.smulLeftCLM ℂ (a i) f
  have hhh : ∀ i x, hh i x = (β (x ∘ Sum.inr) : ℂ) * (∫ s in Ioc (0 : ℝ) 1, d i (Ain s x)) + a i x * f x := by
    intro i x
    simp only [hh, SchwartzMap.add_apply, hN, SchwartzMap.smulLeftCLM_apply_apply (ha i), smul_eq_mul]
  refine ⟨Module.finrank ℝ (κ'' → W), L, hh, fun i => SchwartzMap.smulLeftCLM ℂ
    (fun x : κ' ⊕ κ'' → W => (L i (x ∘ Sum.inr) : ℂ)) (hh i),
    fun i x => by rw [SchwartzMap.smulLeftCLM_apply_apply (hLc i), smul_eq_mul], fun x => ?_⟩
  simp only [SchwartzMap.smulLeftCLM_apply_apply (hLc _), smul_eq_mul, hhh]
  have e1 : ∀ i, (L i (x ∘ Sum.inr) : ℂ) * ((β (x ∘ Sum.inr) : ℂ) * (∫ s in Ioc (0 : ℝ) 1, d i (Ain s x)) + a i x * f x) =
      (β (x ∘ Sum.inr) : ℂ) * ((L i (x ∘ Sum.inr) : ℂ) * ∫ s in Ioc (0 : ℝ) 1, d i (Ain s x)) +
        ((L i (x ∘ Sum.inr) ^ 2 * GlobalTheory.SchwartzDiv.invCut (q (x ∘ Sum.inr)) : ℝ) : ℂ) * f x := by
    intro i; simp only [a]; push_cast; ring
  rw [Finset.sum_congr rfl fun i _ => e1 i, Finset.sum_add_distrib, ← Finset.mul_sum, ← key x,
    ← Finset.sum_mul, ← Complex.ofReal_sum, ← Finset.sum_mul]
  simp only [β, q]
  push_cast
  ring

end PositivityTheory.SiegelWeilFormula.Ald.PCI

end
