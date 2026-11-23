import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.FormulaF
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiExistsOfFormula
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.FunctA

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem psi_funct {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
    {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) :
    ∀ g ∈ UJset ε, ∀ x ∈ UJset ε,
      ((Module.finrank ℂ T.V : ℂ) / ((S7.muK ε Set.univ).toReal : ℂ)) •
          ∫ k, star (LinearMap.trace ℂ T.V (T.op k).toLinearMap) • Ψ (g * S7.toMK k * x) ∂(S7.muK ε) =
        Ψ g * Ψ x := by
  intro g hg x hx
  have hw : T.w ≠ 0 := HW.KType.w_ne_zero T
  set C : ℂ := ((‖uniformisationL2 ε Ψ T.w T.w‖ ^ 2 : ℝ) : ℂ) with hCdef
  have hC0 : C ≠ 0 := by
    have h := datumEmbedding_highest_ne_zero (v₀ := T.w) hgap hP hw
    rw [hCdef]
    exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.2 h)
  have hF : ∀ {h : Matrix (Fin n) (Fin n) ℂ}, h ∈ UJset ε → ∀ v v' : T.V,
      ⟪uniformisationL2 ε Ψ T.w v', rreg ε h (uniformisationL2 ε Ψ T.w v)⟫_ℂ = C * ⟪v', Ψ h v⟫_ℂ :=
    fun hh v v' => formulaF hgap hP hw hh v v'
  have hσ := rreg_isURepOn ε
  have hmem : ∀ k : S7.KG ε, g * S7.toMK k * x ∈ UJset ε :=
    fun k => mul_mem_unitaryJ (mul_mem_unitaryJ hg (fct_toMK_mem k)) hx
  have hcontΨ : Continuous fun k : S7.KG ε => Ψ (g * S7.toMK k * x) :=
    (pdA_continuousOn hP.2.2.1).comp_continuous ((continuous_const.mul fct_cont_toMK).mul continuous_const) hmem
  have hInt : Integrable (fun k : S7.KG ε =>
      star (LinearMap.trace ℂ T.V (T.op k).toLinearMap) • Ψ (g * S7.toMK k * x)) (S7.muK ε) :=
    fct_integrable ((fct_cont_char T).smul hcontΨ)
  refine ContinuousLinearMap.ext fun v => ext_inner_left ℂ fun v' => ?_
  rw [ContinuousLinearMap.smul_apply, inner_smul_right, ContinuousLinearMap.mul_apply]

  have hL : ⟪v', (∫ k, star (LinearMap.trace ℂ T.V (T.op k).toLinearMap) • Ψ (g * S7.toMK k * x)
      ∂(S7.muK ε)) v⟫_ℂ = ∫ k, star (LinearMap.trace ℂ T.V (T.op k).toLinearMap) *
        ⟪v', Ψ (g * S7.toMK k * x) v⟫_ℂ ∂(S7.muK ε) := by
    let L : (T.V →L[ℂ] T.V) →L[ℂ] ℂ := (innerSL ℂ v').comp (ContinuousLinearMap.apply ℂ T.V v)
    have e1 := ContinuousLinearMap.integral_comp_comm L hInt
    have e2 : ∀ B : T.V →L[ℂ] T.V, L B = ⟪v', B v⟫_ℂ := fun B => rfl
    rw [← e2, ← e1]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    show L _ = _
    rw [e2, ContinuousLinearMap.smul_apply, inner_smul_right]
  rw [hL]

  set a : T.V := Ψ x v with ha
  set r : L2 ε := rreg ε x (uniformisationL2 ε Ψ T.w v) - uniformisationL2 ε Ψ T.w a with hr
  set y : L2 ε := ContinuousLinearMap.adjoint (rreg ε g) (uniformisationL2 ε Ψ T.w v') with hy
  set b : T.V := ContinuousLinearMap.adjoint (Ψ g) v' with hb
  have hrmem : r ∈ Hlam ε Ψ T.w :=
    Submodule.sub_mem _ (fct_Hlam_stable hgap hP hw hx (datumEmbedding_mem_Hlam hP v)) (datumEmbedding_mem_Hlam hP a)
  have hrorth : ∀ c, ⟪uniformisationL2 ε Ψ T.w c, r⟫_ℂ = 0 := by
    intro c
    have h1 := hF (one_mem_unitaryJ ε) a c
    rw [hσ.1.1, ContinuousLinearMap.one_apply, hP.2.1, ContinuousLinearMap.one_apply] at h1
    rw [hr, inner_sub_right, hF hx v c, h1, ha, sub_self]
  have hpt : ∀ k : S7.KG ε, C * ⟪v', Ψ (g * S7.toMK k * x) v⟫_ℂ =
      C * ⟪b, T.op k a⟫_ℂ + ⟪y, rreg ε (S7.toMK k) r⟫_ℂ := by
    intro k
    rw [← hF (hmem k) v v', hσ.1.2 _ (mul_mem_unitaryJ hg (fct_toMK_mem k)) _ hx,
      hσ.1.2 _ hg _ (fct_toMK_mem k)]
    simp only [ContinuousLinearMap.comp_apply]
    have hsplit : rreg ε x (uniformisationL2 ε Ψ T.w v) = uniformisationL2 ε Ψ T.w a + r := by rw [hr]; abel
    rw [hsplit, map_add, map_add, inner_add_right, rightRegular_datumEmbedding hP, hF hg, hy, hb,
      ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left]
  have hI1 : Integrable (fun k : S7.KG ε => star (LinearMap.trace ℂ T.V (T.op k).toLinearMap) *
      ⟪b, T.op k a⟫_ℂ) (S7.muK ε) :=
    fct_integrable ((fct_cont_char T).mul (continuous_const.inner ((CompactHaarProbability.cont_op T).clm_apply continuous_const)))
  have hI2 : Integrable (fun k : S7.KG ε => star (LinearMap.trace ℂ T.V (T.op k).toLinearMap) *
      ⟪y, rreg ε (S7.toMK k) r⟫_ℂ) (S7.muK ε) :=
    fct_integrable ((fct_cont_char T).mul (continuous_const.inner (fct_cont_R r)))
  have hI : ∫ k, star (LinearMap.trace ℂ T.V (T.op k).toLinearMap) * ⟪v', Ψ (g * S7.toMK k * x) v⟫_ℂ
      ∂(S7.muK ε) = ∫ k, star (LinearMap.trace ℂ T.V (T.op k).toLinearMap) * ⟪b, T.op k a⟫_ℂ ∂(S7.muK ε) +
        C⁻¹ * ∫ k, star (LinearMap.trace ℂ T.V (T.op k).toLinearMap) * ⟪y, rreg ε (S7.toMK k) r⟫_ℂ
          ∂(S7.muK ε) := by
    rw [← integral_const_mul, ← integral_add hI1 (hI2.const_mul _)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    have h3 : ⟪v', Ψ (g * S7.toMK k * x) v⟫_ℂ = ⟪b, T.op k a⟫_ℂ + C⁻¹ * ⟪y, rreg ε (S7.toMK k) r⟫_ℂ := by
      rw [← mul_right_inj' hC0, mul_add, hpt k, ← mul_assoc, mul_inv_cancel₀ hC0, one_mul]
    dsimp only
    rw [h3]
    ring
  rw [hI, fct_key hgap hP hw hrmem hrorth y, mul_zero, add_zero, fct_char T b a, hb,
    ContinuousLinearMap.adjoint_inner_left]

end ReciprocityTheory.ChartRestriction.DS
