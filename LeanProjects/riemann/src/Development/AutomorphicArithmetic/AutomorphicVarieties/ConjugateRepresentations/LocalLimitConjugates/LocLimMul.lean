import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

section

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

private noncomputable def cj (χ : HChar E) (T : Module.End ℂ (Sm E a)) : Module.End ℂ (Sm E a) :=
  (mulChi a χ).symm.toLinearMap ∘ₗ T ∘ₗ (mulChi a χ).toLinearMap

private theorem mul_cj (χ : HChar E) (T : Module.End ℂ (Sm E a)) (φ : Sm E a) :
    mulChi a χ (cj χ T φ) = T (mulChi a χ φ) := (mulChi a χ).apply_symm_apply _

private theorem isOp_cj {r : ℝ} {χ : HChar E} (hχ : IsTw (a := a) r χ) {N : Submodule ℂ (Sm E a)}
    {T : Module.End ℂ (Sm E a)} (hT : IsOp N T) : IsOp (N.comap (mulChi a χ).toLinearMap) (cj χ T) where
  maps φ hφ := by
    change mulChi a χ (cj χ T φ) ∈ N
    rw [mul_cj]
    exact hT.maps _ hφ
  lie X φ hφ := by
    apply (mulChi a χ).injective
    have h1 := hT.lie X _ hφ
    have h2 := hχ.2 X (cj χ T φ)
    change lie E a X (T (mulChi a χ φ)) = T (lie E a X (mulChi a χ φ)) at h1
    rw [mul_cj, h1, hχ.2, map_add, map_add, map_add, map_smul, map_smul, map_smul, mul_cj] at h2
    rw [mul_cj]
    exact (add_right_cancel h2).symm
  rt g φ hφ := by
    apply (mulChi a χ).injective
    have h1 := hT.rt g _ hφ
    have h2 := rt_mulChi χ g (cj χ T φ)
    change rt E a g (T (mulChi a χ φ)) = T (rt E a g (mulChi a χ φ)) at h1
    rw [mul_cj, h1, rt_mulChi, map_smul, map_smul, map_smul] at h2
    rw [mul_cj]
    exact (smul_right_injective _ (chiDet a χ g).ne_zero h2).symm

private theorem shift_mul {r : ℝ} {χ : HChar E} (hχ : IsTw (a := a) r χ) (X : Lie E a) (φ : Sm E a) :
    shift (lie E a) 0 X (mulChi a χ φ) = mulChi a χ (shift (lie E a) r X φ) := by
  rw [shift_apply, shift_apply, zero_mul, zero_smul, add_zero, hχ.2, LinearMap.add_apply, LinearMap.smul_apply,
    Module.End.one_apply, Complex.coe_smul]

private theorem casA_mul {r : ℝ} {χ : HChar E} (hχ : IsTw (a := a) r χ) (c : ℝ) {n : ℕ} (e : Fin n → Herm E a)
    (φ : Sm E a) : casA 0 c e (mulChi a χ φ) = mulChi a χ (casA r c e φ) := by
  simp only [casA, cas, LinearMap.sub_apply, LinearMap.sum_apply, Module.End.mul_apply, LinearMap.smul_apply,
    Module.End.one_apply, map_sub, map_sum, map_smul, shift_mul hχ]

private theorem locLim_mul (χ : HChar E) {f : ℕ → Sm E a} {φ : Sm E a}
    (h : LocLim (fun k => mulChi a χ (f k)) (mulChi a χ φ)) : LocLim f φ := by
  intro C hC
  have hc : Continuous fun g : GA E a => (((chiDet a χ g)⁻¹ : ℂˣ) : ℂ) :=
    Units.continuous_val.comp (χ.2.1.comp Matrix.GeneralLinearGroup.continuous_det).inv
  obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn hc.continuousOn
  have h1 := h C hC
  rw [Metric.tendstoUniformlyOn_iff] at h1 ⊢
  intro ε hε
  have hp : 0 < |B| + 1 := by positivity
  filter_upwards [h1 (ε / (|B| + 1)) (by positivity)] with k hk g hg
  have h2 := hk g hg
  rw [dist_eq_norm, mulChi_apply, mulChi_apply, ← sub_mul, lt_div_iff₀ hp] at h2
  have e : φ.1 g - (f k).1 g = (φ.1 g - (f k).1 g) * (chiDet a χ g : ℂˣ) * (((chiDet a χ g)⁻¹ : ℂˣ) : ℂ) :=
    (Units.mul_inv_cancel_right _ _).symm
  rw [dist_eq_norm, e, norm_mul]
  refine lt_of_le_of_lt (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)) h2
  exact (hB g hg).trans ((le_abs_self B).trans (le_add_of_nonneg_right zero_le_one))

end

theorem UpperTheory.V.Cj.H.twRes :
    UpperTheory.V.Cj.H.TwRes := by
  intro E _ _ _ a r χ hχ N n e c P Q S h
  refine ⟨cj χ P, fun k => cj χ (Q k), fun k => cj χ (S k), isOp_cj hχ h.opP, fun k => isOp_cj hχ (h.opQ k),
    fun k => isOp_cj hχ (h.opS k), fun k φ hφ => ?_, fun φ hφ => ?_, fun φ hφ => ?_⟩
  · apply (mulChi a χ).injective
    rw [map_sub, ← casA_mul hχ, mul_cj, mul_cj]
    exact h.res k _ hφ
  · apply (mulChi a χ).injective
    rw [map_zero, ← casA_mul hχ, mul_cj]
    exact h.ker _ hφ
  · apply locLim_mul χ
    simp only [mul_cj]
    exact h.lim _ hφ
