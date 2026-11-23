import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumEmbeddingMemHlam
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.ClosGenStable
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.KSchur

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open CompactHaarProbability

variable {n : ℕ}

section Schur

variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}

theorem fct_op_inner (T : S7.KType ε Λ) (k : S7.KG ε) (x y : T.V) :
    ⟪T.op k x, T.op k y⟫_ℂ = ⟪x, y⟫_ℂ := by
  rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.mul_apply,
    ← ContinuousLinearMap.star_eq_adjoint, Unitary.star_mul_self_of_mem (T.τ k).2,
    ContinuousLinearMap.one_apply]

theorem fct_integrable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : S7.KG ε → E}
    (hf : Continuous f) : Integrable f (S7.muK ε) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem fct_cont_char (T : S7.KType ε Λ) :
    Continuous fun k : S7.KG ε => star (LinearMap.trace ℂ T.V (T.op k).toLinearMap) := by
  let tr : (T.V →L[ℂ] T.V) →L[ℂ] ℂ :=
    LinearMap.toContinuousLinearMap (LinearMap.trace ℂ T.V ∘ₗ ContinuousLinearMap.coeLM ℂ)
  exact (tr.continuous.comp (cont_op T)).star

theorem fct_trace_star (T : S7.KType ε Λ) (k : S7.KG ε) :
    star (LinearMap.trace ℂ T.V (T.op k).toLinearMap) =
      ∑ a, ⟪T.op k (stdOrthonormalBasis ℂ T.V a), stdOrthonormalBasis ℂ T.V a⟫_ℂ := by
  rw [LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℂ T.V), star_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact inner_conj_symm _ _

theorem fct_int_dk {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : S7.KG ε → E) :
    ∫ k, f k ∂(dk ε) = ((S7.muK ε Set.univ).toReal)⁻¹ • ∫ k, f k ∂(S7.muK ε) := by
  rw [dk, integral_smul_measure, ENNReal.toReal_inv]

theorem fct_schur_gen (T : S7.KType ε Λ) (P : T.V →L[ℂ] T.V) :
    ((Module.finrank ℂ T.V : ℂ) / ((S7.muK ε Set.univ).toReal : ℂ)) •
        ∫ k, T.op k * P * T.op k⁻¹ ∂(S7.muK ε) =
      LinearMap.trace ℂ T.V (P : T.V →ₗ[ℂ] T.V) • (1 : T.V →L[ℂ] T.V) := by
  set A : T.V →L[ℂ] T.V := ∫ k, T.op k * P * T.op k⁻¹ ∂(dk ε) with hAdef
  have hcomm : ∀ k, T.op k * A = A * T.op k := by
    intro k
    have h := int_conj T P k
    rw [← hAdef] at h
    calc T.op k * A = T.op k * A * (T.op k⁻¹ * T.op k) := by rw [op_inv_mul, mul_one]
      _ = (T.op k * A * T.op k⁻¹) * T.op k := by simp only [mul_assoc]
      _ = A * T.op k := by rw [h]
  obtain ⟨a, ha⟩ := schur T A hcomm
  let tr : (T.V →L[ℂ] T.V) →L[ℂ] ℂ :=
    LinearMap.toContinuousLinearMap (LinearMap.trace ℂ T.V ∘ₗ ContinuousLinearMap.coeLM ℂ)
  have htr_apply : ∀ B : T.V →L[ℂ] T.V, tr B = LinearMap.trace ℂ T.V (B : T.V →ₗ[ℂ] T.V) :=
    fun B => rfl
  have htrP : ∀ k, tr (T.op k * P * T.op k⁻¹) = LinearMap.trace ℂ T.V (P : T.V →ₗ[ℂ] T.V) := by
    intro k
    rw [htr_apply, ContinuousLinearMap.toLinearMap_mul, LinearMap.trace_mul_comm,
      ← ContinuousLinearMap.toLinearMap_mul, ← mul_assoc, op_inv_mul, one_mul]
  have htrA : tr A = LinearMap.trace ℂ T.V (P : T.V →ₗ[ℂ] T.V) := by
    rw [hAdef, ← ContinuousLinearMap.integral_comp_comm _ (integrable_conj T _)]
    simp only [htrP, integral_const, probReal_univ, one_smul]
  have hd : (Module.finrank ℂ T.V : ℂ) ≠ 0 := by
    have : Nontrivial T.V := ⟨⟨T.w, 0, fun h => by
      have := T.w_norm; rw [h, norm_zero] at this; exact zero_ne_one this⟩⟩
    exact_mod_cast (Module.finrank_pos (R := ℂ) (M := T.V)).ne'
  have htra : tr A = a * (Module.finrank ℂ T.V : ℂ) := by
    rw [ha, map_smul, htr_apply, ContinuousLinearMap.toLinearMap_one, LinearMap.trace_one,
      smul_eq_mul]
  have hvol : ((S7.muK ε Set.univ).toReal : ℂ) ≠ 0 := by
    exact_mod_cast (S7.muK_univ_pos ε).ne'
  have hA : ∫ k, T.op k * P * T.op k⁻¹ ∂(S7.muK ε) = ((S7.muK ε Set.univ).toReal : ℂ) • A := by
    rw [hAdef, fct_int_dk, Complex.coe_smul, smul_smul, mul_inv_cancel₀ (S7.muK_univ_pos ε).ne', one_smul]
  rw [hA, smul_smul, ha, smul_smul]
  congr 1
  have : a = LinearMap.trace ℂ T.V (P : T.V →ₗ[ℂ] T.V) / (Module.finrank ℂ T.V : ℂ) := by
    rw [← htrA, htra]; field_simp
  rw [this]
  field_simp

theorem fct_char (T : S7.KType ε Λ) (b c : T.V) :
    ((Module.finrank ℂ T.V : ℂ) / ((S7.muK ε Set.univ).toReal : ℂ)) *
        ∫ k, star (LinearMap.trace ℂ T.V (T.op k).toLinearMap) * ⟪b, T.op k c⟫_ℂ ∂(S7.muK ε) =
      ⟪b, c⟫_ℂ := by
  set e := stdOrthonormalBasis ℂ T.V
  let P : Fin (Module.finrank ℂ T.V) → T.V →L[ℂ] T.V := fun a => (innerSL ℂ (e a)).smulRight c
  let Lf : Fin (Module.finrank ℂ T.V) → (T.V →L[ℂ] T.V) →L[ℂ] ℂ :=
    fun a => (innerSL ℂ b).comp (ContinuousLinearMap.apply ℂ T.V (e a))
  have hLf : ∀ a (B : T.V →L[ℂ] T.V), Lf a B = ⟪b, B (e a)⟫_ℂ := fun a B => rfl
  have hpt : ∀ k, star (LinearMap.trace ℂ T.V (T.op k).toLinearMap) * ⟪b, T.op k c⟫_ℂ =
      ∑ a, Lf a (T.op k * P a * T.op k⁻¹) := by
    intro k
    rw [fct_trace_star, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hLf]
    simp only [ContinuousLinearMap.mul_apply, P, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
      map_smul, inner_smul_right]
    congr 1
    rw [← fct_op_inner T k (e a) (T.op k⁻¹ (e a)), ← ContinuousLinearMap.mul_apply, op_mul_inv,
      ContinuousLinearMap.one_apply]
  have hint : ∀ a, Integrable (fun k => T.op k * P a * T.op k⁻¹) (S7.muK ε) :=
    fun a => fct_integrable (cont_conj T _)
  simp_rw [hpt]
  rw [integral_finsetSum _ (fun a _ => (fct_integrable ((Lf a).continuous.comp (cont_conj T (P a))) :
    Integrable (fun k => Lf a (T.op k * P a * T.op k⁻¹)) (S7.muK ε))), Finset.mul_sum]
  have h1 : ∀ a, ((Module.finrank ℂ T.V : ℂ) / ((S7.muK ε Set.univ).toReal : ℂ)) *
      ∫ k, Lf a (T.op k * P a * T.op k⁻¹) ∂(S7.muK ε) = ⟪e a, c⟫_ℂ * ⟪b, e a⟫_ℂ := by
    intro a
    rw [ContinuousLinearMap.integral_comp_comm _ (hint a), ← smul_eq_mul, ← map_smul, fct_schur_gen, map_smul, hLf,
      ContinuousLinearMap.one_apply, smul_eq_mul]
    congr 1
    simp [P, LinearMap.trace_smulRight]
  simp_rw [h1]
  rw [← e.sum_inner_mul_inner b c]
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

end Schur

section Theta

variable {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V}

theorem fct_toMK_mem (k : S7.KG ε) : S7.toMK k ∈ UJset ε := k.1.2

theorem fct_cont_toMK : Continuous fun k : S7.KG ε => S7.toMK k :=
  (S7.continuous_toM ε).comp continuous_subtype_val

theorem fct_cont_R (r : L2 ε) : Continuous fun k : S7.KG ε => rreg ε (S7.toMK k) r :=
  ((rreg_isURepOn ε).2.2 r).comp_continuous fct_cont_toMK fct_toMK_mem

theorem fct_rreg_inner {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) (x y : L2 ε) :
    ⟪rreg ε g x, rreg ε g y⟫_ℂ = ⟪x, y⟫_ℂ := by
  let f : L2 ε →ₗᵢ[ℂ] L2 ε := { toLinearMap := (rreg ε g).toLinearMap, norm_map' := (rreg_isURepOn ε).2.1 g hg }
  exact f.inner_map_map x y

def fctTheta (T : S7.KType ε (lowK ε lam)) (r : L2 ε) (e p : T.V) : L2 ε :=
  ∫ k, ⟪T.op k e, p⟫_ℂ • rreg ε (S7.toMK k) r ∂(S7.muK ε)

theorem fct_cont_integrand (r : L2 ε) (e p : T.V) :
    Continuous fun k : S7.KG ε => ⟪T.op k e, p⟫_ℂ • rreg ε (S7.toMK k) r :=
  by
    have h1 : Continuous fun k : S7.KG ε => ⟪T.op k e, p⟫_ℂ :=
      ((cont_op T).clm_apply continuous_const).inner continuous_const
    exact h1.smul (fct_cont_R r)

theorem fct_theta_add (r : L2 ε) (e p q : T.V) :
    fctTheta T r e (p + q) = fctTheta T r e p + fctTheta T r e q := by
  unfold fctTheta
  rw [← integral_add (fct_integrable (fct_cont_integrand r e p)) (fct_integrable (fct_cont_integrand r e q))]
  congr 1
  funext k
  rw [inner_add_right, add_smul]

theorem fct_theta_smul (r : L2 ε) (e : T.V) (c : ℂ) (p : T.V) :
    fctTheta T r e (c • p) = c • fctTheta T r e p := by
  unfold fctTheta
  rw [← integral_smul]
  congr 1
  funext k
  rw [inner_smul_right, mul_smul]

def fctThetaLin (T : S7.KType ε (lowK ε lam)) (r : L2 ε) (e : T.V) : T.V →ₗ[ℂ] L2 ε where
  toFun := fctTheta T r e
  map_add' := fct_theta_add r e
  map_smul' := fct_theta_smul r e

theorem fct_theta_equiv (r : L2 ε) (e p : T.V) (k' : S7.KG ε) :
    fctTheta T r e (T.op k' p) = rreg ε (S7.toMK k') (fctTheta T r e p) := by
  unfold fctTheta
  conv_lhs => rw [← integral_mul_left_eq_self _ k']
  rw [← ContinuousLinearMap.integral_comp_comm _ (fct_integrable (fct_cont_integrand r e p))]
  congr 1
  funext k
  rw [op_mul, ContinuousLinearMap.mul_apply, fct_op_inner, map_smul]
  congr 1
  show rreg ε (S7.toMK k' * S7.toMK k) r = _
  rw [(rreg_isURepOn ε).1.2 _ (fct_toMK_mem k') _ (fct_toMK_mem k)]
  rfl

theorem fct_Hlam_stable (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) {x : L2 ε} (hx : x ∈ Hlam ε Ψ v₀) :
    rreg ε g x ∈ Hlam ε Ψ v₀ :=
  closGen_stable hgap (rreg_isURepOn ε) (isDerivedOn_smE (rreg_isURepOn ε)) (datumV_isKIrrHW hP hv₀)
    (datumV_casimir hP v₀) (datumV_kStable hP v₀) g hg x hx

theorem fct_theta_mem (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) {r : L2 ε}
    (hr : r ∈ Hlam ε Ψ v₀) (e p : T.V) : fctTheta T r e p ∈ Hlam ε Ψ v₀ := by
  rw [← Submodule.orthogonal_orthogonal (Hlam ε Ψ v₀), Submodule.mem_orthogonal]
  intro z hz
  unfold fctTheta
  rw [← integral_inner (fct_integrable (fct_cont_integrand r e p))]
  refine (integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)).trans (integral_zero _ _)
  show ⟪z, ⟪T.op k e, p⟫_ℂ • rreg ε (S7.toMK k) r⟫_ℂ = 0
  rw [inner_smul_right, Submodule.inner_left_of_mem_orthogonal
    (fct_Hlam_stable hgap hP hv₀ (fct_toMK_mem k) hr) hz, mul_zero]

theorem fct_theta_orth (hP : IsPsiFor ε lam T Ψ) {r : L2 ε}
    (horth : ∀ b, ⟪uniformisationL2 ε Ψ v₀ b, r⟫_ℂ = 0) (e p q : T.V) :
    ⟪uniformisationL2 ε Ψ v₀ q, fctTheta T r e p⟫_ℂ = 0 := by
  unfold fctTheta
  rw [← integral_inner (fct_integrable (fct_cont_integrand r e p))]
  refine (integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)).trans (integral_zero _ _)
  show ⟪uniformisationL2 ε Ψ v₀ q, ⟪T.op k e, p⟫_ℂ • rreg ε (S7.toMK k) r⟫_ℂ = 0
  have hq : uniformisationL2 ε Ψ v₀ q = rreg ε (S7.toMK k) (uniformisationL2 ε Ψ v₀ (T.op k⁻¹ q)) := by
    rw [rightRegular_datumEmbedding hP, ← ContinuousLinearMap.mul_apply, op_mul_inv, ContinuousLinearMap.one_apply]
  rw [inner_smul_right, hq, fct_rreg_inner (fct_toMK_mem k), horth, mul_zero]

theorem fct_theta_zero (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) {r : L2 ε}
    (hr : r ∈ Hlam ε Ψ v₀) (horth : ∀ b, ⟪uniformisationL2 ε Ψ v₀ b, r⟫_ℂ = 0) (e p : T.V) :
    fctTheta T r e p = 0 := by
  let eqv : T.V ≃ₗ[ℂ] datumV ε Ψ v₀ :=
    (LinearEquiv.ofInjective (jSm hP v₀) (jSm_injective hP hv₀)).trans
      (LinearEquiv.ofEq _ _ (datumV_eq_range hP v₀).symm)
  have heqv : ∀ p, (((eqv p : datumV ε Ψ v₀) : smD ε (rreg ε)) : L2 ε) = uniformisationL2 ε Ψ v₀ p := fun p => rfl
  have hsymm : ∀ w : datumV ε Ψ v₀, (((w : datumV ε Ψ v₀) : smD ε (rreg ε)) : L2 ε) =
      uniformisationL2 ε Ψ v₀ (eqv.symm w) := fun w => by rw [← heqv, LinearEquiv.apply_symm_apply]
  let j' : datumV ε Ψ v₀ →ₗ[ℂ] L2 ε := (fctThetaLin T r e) ∘ₗ eqv.symm.toLinearMap
  have hj'_apply : ∀ w, j' w = fctTheta T r e (eqv.symm w) := fun w => rfl
  have h0 := rigid_multOne hgap (rreg_isURepOn ε) (isDerivedOn_smE (rreg_isURepOn ε))
    (datumV_isKIrrHW hP hv₀) (datumV_casimir hP v₀) (datumV_kStable hP v₀) j' ?hj ?hrange ?horth
  · have := LinearMap.congr_fun h0 (eqv p)
    rwa [hj'_apply, LinearEquiv.symm_apply_apply, LinearMap.zero_apply] at this
  case hj =>
    intro k hk v w hvw
    have hk' : S7.toMK (pdA_kg k hk) = k := pdA_toMK_kg k hk
    rw [hsymm, hsymm, ← hk', rightRegular_datumEmbedding hP] at hvw
    have hq := uniformisationL2_injective hP hv₀ hvw
    rw [hj'_apply, hj'_apply, hq, fct_theta_equiv, hk']
  case hrange =>
    intro v
    exact fct_theta_mem hgap hP hv₀ hr e _
  case horth =>
    intro v v'
    rw [hsymm, hj'_apply]
    exact inner_eq_zero_symm.mp (fct_theta_orth hP horth e _ _)

theorem fct_key (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) {r : L2 ε}
    (hr : r ∈ Hlam ε Ψ v₀) (horth : ∀ b, ⟪uniformisationL2 ε Ψ v₀ b, r⟫_ℂ = 0) (y : L2 ε) :
    ∫ k, star (LinearMap.trace ℂ T.V (T.op k).toLinearMap) * ⟪y, rreg ε (S7.toMK k) r⟫_ℂ ∂(S7.muK ε) = 0 := by
  set e := stdOrthonormalBasis ℂ T.V
  have hpt : ∀ k, star (LinearMap.trace ℂ T.V (T.op k).toLinearMap) * ⟪y, rreg ε (S7.toMK k) r⟫_ℂ =
      ∑ a, ⟪y, ⟪T.op k (e a), e a⟫_ℂ • rreg ε (S7.toMK k) r⟫_ℂ := by
    intro k
    rw [fct_trace_star, Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => (inner_smul_right _ _ _).symm
  simp_rw [hpt]
  rw [integral_finsetSum _ (fun a _ => fct_integrable
    (continuous_const.inner (fct_cont_integrand r (e a) (e a))))]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [integral_inner (fct_integrable (fct_cont_integrand r (e a) (e a)))]
  show ⟪y, fctTheta T r (e a) (e a)⟫_ℂ = 0
  rw [fct_theta_zero hgap hP hv₀ hr horth, inner_zero_right]

end Theta

end ReciprocityTheory.ChartRestriction.DS
