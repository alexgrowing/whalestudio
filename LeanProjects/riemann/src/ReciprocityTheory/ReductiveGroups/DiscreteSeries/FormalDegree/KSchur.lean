import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PmatIsHermitian
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.KinstSecondCountable

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace ENNReal

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

namespace CompactHaarProbability

variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}

lemma muK_univ_ne_zero (ε : Fin n → Bool) : muK ε Set.univ ≠ 0 := ((ENNReal.toReal_pos_iff.mp (muK_univ_pos ε)).1).ne'

lemma muK_univ_ne_top (ε : Fin n → Bool) : muK ε Set.univ ≠ ⊤ := ((ENNReal.toReal_pos_iff.mp (muK_univ_pos ε)).2).ne

instance dk_isProb (ε : Fin n → Bool) : IsProbabilityMeasure (dk ε) :=
  ⟨by simp [dk]⟩

instance dk_left (ε : Fin n → Bool) : (dk ε).IsMulLeftInvariant := by
  unfold dk; infer_instance

instance dk_right (ε : Fin n → Bool) : (dk ε).IsMulRightInvariant := by
  have := muK_rightInvariant ε
  unfold dk; infer_instance

lemma muK_inv (ε : Fin n → Bool) : Measure.map (fun x : KG ε => x⁻¹) (muK ε) = muK ε := by
  haveI := muK_rightInvariant ε
  set ν := Measure.map (fun x : KG ε => x⁻¹) (muK ε) with hν
  haveI : ν.IsMulLeftInvariant := by
    change (muK ε).inv.IsMulLeftInvariant
    infer_instance
  haveI : IsFiniteMeasure ν := by rw [hν]; infer_instance
  have e := Measure.isMulInvariant_eq_smul_of_compactSpace ν (muK ε)
  have huniv : ν Set.univ = muK ε Set.univ := by
    rw [hν, Measure.map_apply measurable_inv MeasurableSet.univ, Set.preimage_univ]
  rw [e] at huniv
  rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at huniv
  have hc : (ν.haarScalarFactor (muK ε) : ℝ≥0∞) = 1 := by
    have h2 := congrArg (· / muK ε Set.univ) huniv
    rwa [ENNReal.mul_div_cancel_right (muK_univ_ne_zero ε) (muK_univ_ne_top ε),
      ENNReal.div_self (muK_univ_ne_zero ε) (muK_univ_ne_top ε)] at h2
  have hc' : ν.haarScalarFactor (muK ε) = 1 := by exact_mod_cast hc
  rw [e, hc', one_smul]

lemma dk_inv (ε : Fin n → Bool) : Measure.map (fun x : KG ε => x⁻¹) (dk ε) = dk ε := by
  unfold dk
  rw [Measure.map_smul, muK_inv]

end CompactHaarProbability

open CompactHaarProbability in

theorem dk_props (ε : Fin n → Bool) :
    IsProbabilityMeasure (dk ε) ∧ (∀ k : KG ε, Measure.map (fun x => k * x) (dk ε) = dk ε) ∧
      (∀ k : KG ε, Measure.map (fun x => x * k) (dk ε) = dk ε) ∧
      Measure.map (fun x : KG ε => x⁻¹) (dk ε) = dk ε := by
  refine ⟨inferInstance, fun k => map_mul_left_eq_self (dk ε) k, fun k => map_mul_right_eq_self (dk ε) k,
    dk_inv ε⟩

namespace CompactHaarProbability

variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}

lemma op_mul (T : KType ε Λ) (a b : KG ε) : T.op (a * b) = T.op a * T.op b := by
  show ((T.τ (a * b) : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) = _
  rw [map_mul]
  rfl

lemma op_one (T : KType ε Λ) : T.op 1 = 1 := by
  show ((T.τ 1 : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) = 1
  rw [map_one]
  rfl

lemma op_mul_inv (T : KType ε Λ) (a : KG ε) : T.op a * T.op a⁻¹ = 1 := by
  rw [← op_mul, mul_inv_cancel, op_one]

lemma op_inv_mul (T : KType ε Λ) (a : KG ε) : T.op a⁻¹ * T.op a = 1 := by
  rw [← op_mul, inv_mul_cancel, op_one]

def opE (T : KType ε Λ) (k : KG ε) : T.V ≃L[ℂ] T.V :=
  ContinuousLinearEquiv.equivOfInverse (T.op k) (T.op k⁻¹)
    (fun v => by
      have := congrArg (fun A : T.V →L[ℂ] T.V => A v) (op_inv_mul T k)
      simpa using this)
    (fun v => by
      have := congrArg (fun A : T.V →L[ℂ] T.V => A v) (op_mul_inv T k)
      simpa using this)

def conjE (T : KType ε Λ) (k : KG ε) : (T.V →L[ℂ] T.V) ≃L[ℂ] (T.V →L[ℂ] T.V) :=
  (opE T k).arrowCongr (opE T k)

lemma conjE_apply (T : KType ε Λ) (k : KG ε) (A : T.V →L[ℂ] T.V) :
    conjE T k A = T.op k * A * T.op k⁻¹ := by
  exact ContinuousLinearMap.ext fun v => rfl

lemma schur (T : KType ε Λ) (A : T.V →L[ℂ] T.V) (hA : ∀ k, T.op k * A = A * T.op k) :
    ∃ c : ℂ, A = c • (1 : T.V →L[ℂ] T.V) := by
  by_cases hV : Nontrivial T.V
  · obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (A : T.V →ₗ[ℂ] T.V)
    have hinv : ∀ k : KG ε, ∀ v ∈ Module.End.eigenspace (A : T.V →ₗ[ℂ] T.V) c,
        ((T.τ k : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) v ∈
          Module.End.eigenspace (A : T.V →ₗ[ℂ] T.V) c := by
      intro k v hv
      rw [Module.End.mem_eigenspace_iff] at hv ⊢
      have e := congrArg (fun B : T.V →L[ℂ] T.V => B v) (hA k)
      simp only [ContinuousLinearMap.mul_apply] at e
      change A (T.op k v) = c • T.op k v
      rw [← e]
      change T.op k ((A : T.V →ₗ[ℂ] T.V) v) = _
      rw [hv, map_smul]
    rcases T.irred _ hinv with h | h
    · obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
      exact absurd ((Submodule.mem_bot ℂ).mp (h ▸ hv.1)) hv.2
    · refine ⟨c, ContinuousLinearMap.ext fun v => ?_⟩
      have hv : v ∈ Module.End.eigenspace (A : T.V →ₗ[ℂ] T.V) c := h ▸ Submodule.mem_top
      rw [Module.End.mem_eigenspace_iff] at hv
      simpa using hv
  · haveI : Subsingleton T.V := not_nontrivial_iff_subsingleton.mp hV
    exact ⟨0, ContinuousLinearMap.ext fun v => Subsingleton.elim _ _⟩

lemma cont_op (T : KType ε Λ) : Continuous fun k : KG ε => T.op k := continuous_subtype_val.comp T.cont

lemma cont_conj (T : KType ε Λ) (P : T.V →L[ℂ] T.V) :
    Continuous fun k : KG ε => T.op k * P * T.op k⁻¹ := ((cont_op T).mul continuous_const).mul ((cont_op T).comp continuous_inv)

lemma integrable_conj (T : KType ε Λ) (P : T.V →L[ℂ] T.V) :
    Integrable (fun k : KG ε => T.op k * P * T.op k⁻¹) (dk ε) := by
  have h := (cont_conj T P).continuousOn.integrableOn_compact (μ := dk ε) isCompact_univ
  rwa [integrableOn_univ] at h

lemma int_conj (T : KType ε Λ) (P : T.V →L[ℂ] T.V) (k : KG ε) :
    T.op k * (∫ k', T.op k' * P * T.op k'⁻¹ ∂(dk ε)) * T.op k⁻¹ =
      ∫ k', T.op k' * P * T.op k'⁻¹ ∂(dk ε) := by
  rw [← conjE_apply, ← ContinuousLinearEquiv.integral_comp_comm]
  simp_rw [conjE_apply]
  have e : ∀ k' : KG ε, T.op k * (T.op k' * P * T.op k'⁻¹) * T.op k⁻¹ =
      T.op (k * k') * P * T.op (k * k')⁻¹ := by
    intro k'
    rw [op_mul, _root_.mul_inv_rev, op_mul]
    simp only [mul_assoc]
  simp_rw [e]
  exact integral_mul_left_eq_self (fun k' => T.op k' * P * T.op k'⁻¹) k

end CompactHaarProbability

open CompactHaarProbability in

theorem kschur_op {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (v : T.V) :
    ((Module.finrank ℂ T.V : ℝ) : ℂ) •
        ∫ k, T.op k * (innerSL ℂ v).smulRight v * T.op k⁻¹ ∂(dk ε) =
      ((‖v‖ ^ 2 : ℝ) : ℂ) • (1 : T.V →L[ℂ] T.V) := by
  set P : T.V →L[ℂ] T.V := (innerSL ℂ v).smulRight v with hP
  set I := ∫ k, T.op k * P * T.op k⁻¹ ∂(dk ε) with hI
  have hcomm : ∀ k, T.op k * I = I * T.op k := by
    intro k
    have h := int_conj T P k
    calc T.op k * I = T.op k * I * (T.op k⁻¹ * T.op k) := by rw [op_inv_mul, mul_one]
      _ = (T.op k * I * T.op k⁻¹) * T.op k := by simp only [mul_assoc]
      _ = I * T.op k := by rw [h]
  obtain ⟨c, hc⟩ := schur T I hcomm
  let tr : (T.V →L[ℂ] T.V) →ₗ[ℂ] ℂ := (LinearMap.trace ℂ T.V).comp (ContinuousLinearMap.coeLM ℂ)
  let trL : (T.V →L[ℂ] T.V) →L[ℂ] ℂ := LinearMap.toContinuousLinearMap tr
  have htr : ∀ A : T.V →L[ℂ] T.V, trL A = LinearMap.trace ℂ T.V (A : T.V →ₗ[ℂ] T.V) := fun A => rfl
  have hconj : ∀ k : KG ε, trL (T.op k * P * T.op k⁻¹) = trL P := by
    intro k
    rw [htr, htr, ContinuousLinearMap.coe_mul, ContinuousLinearMap.coe_mul, mul_assoc,
      LinearMap.trace_mul_comm, mul_assoc, ← ContinuousLinearMap.coe_mul, op_inv_mul]
    simp
  have htrP : trL P = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
    rw [htr, LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℂ T.V)]
    simp only [ContinuousLinearMap.coe_coe, hP, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
      inner_smul_right]
    rw [OrthonormalBasis.sum_inner_mul_inner, inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  have hItr : trL I = trL P := by
    rw [hI, ← ContinuousLinearMap.integral_comp_comm trL (integrable_conj T P)]
    simp_rw [hconj]
    rw [integral_const]
    simp
  have htr1 : trL (c • (1 : T.V →L[ℂ] T.V)) = c * (Module.finrank ℂ T.V : ℂ) := by
    rw [map_smul, htr]
    simp [LinearMap.trace_one]
  rw [hc, htr1, htrP] at hItr
  have key : ((Module.finrank ℂ T.V : ℝ) : ℂ) * c = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
    rw [← hItr]
    push_cast
    ring
  rw [hc, smul_smul, key]

open CompactHaarProbability in

theorem kschur_coef {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (u v : T.V) :
    (Module.finrank ℂ T.V : ℝ) * ∫ k, ‖⟪u, T.op k v⟫_ℂ‖ ^ 2 ∂(dk ε) = ‖v‖ ^ 2 * ‖u‖ ^ 2 := by
  set P : T.V →L[ℂ] T.V := (innerSL ℂ v).smulRight v with hP
  have hop := kschur_op T v
  rw [← hP] at hop
  have hadj : ∀ k : KG ε, T.op k⁻¹ = ContinuousLinearMap.adjoint (T.op k) := by
    intro k
    show ((T.τ k⁻¹ : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) = _
    rw [map_inv, ← ContinuousLinearMap.star_eq_adjoint]
    rfl
  have hpt : ∀ k : KG ε, ⟪u, (T.op k * P * T.op k⁻¹) u⟫_ℂ = ((‖⟪u, T.op k v⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
    intro k
    simp only [ContinuousLinearMap.mul_apply, hP, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
    rw [hadj, ContinuousLinearMap.adjoint_inner_right, map_smul, inner_smul_right, ← inner_conj_symm,
      RCLike.conj_mul]
    push_cast
    rfl
  let E : (T.V →L[ℂ] T.V) →L[ℂ] ℂ := (innerSL ℂ u).comp (ContinuousLinearMap.apply ℂ T.V u)
  have hE : ∀ A : T.V →L[ℂ] T.V, E A = ⟪u, A u⟫_ℂ := fun A => rfl
  have hint : ((∫ k, ‖⟪u, T.op k v⟫_ℂ‖ ^ 2 ∂(dk ε) : ℝ) : ℂ) =
      ⟪u, (∫ k, T.op k * P * T.op k⁻¹ ∂(dk ε)) u⟫_ℂ := by
    rw [← integral_complex_ofReal, ← hE, ← ContinuousLinearMap.integral_comp_comm E (integrable_conj T P)]
    simp_rw [hE, hpt]
  have hfin : ((Module.finrank ℂ T.V : ℝ) : ℂ) * ⟪u, (∫ k, T.op k * P * T.op k⁻¹ ∂(dk ε)) u⟫_ℂ =
      ((‖v‖ ^ 2 * ‖u‖ ^ 2 : ℝ) : ℂ) := by
    calc ((Module.finrank ℂ T.V : ℝ) : ℂ) * ⟪u, (∫ k, T.op k * P * T.op k⁻¹ ∂(dk ε)) u⟫_ℂ
        = ⟪u, (((Module.finrank ℂ T.V : ℝ) : ℂ) • ∫ k, T.op k * P * T.op k⁻¹ ∂(dk ε)) u⟫_ℂ := by
          rw [ContinuousLinearMap.smul_apply, inner_smul_right]
      _ = ⟪u, (((‖v‖ ^ 2 : ℝ) : ℂ) • (1 : T.V →L[ℂ] T.V)) u⟫_ℂ := by rw [hop]
      _ = ((‖v‖ ^ 2 : ℝ) : ℂ) * ⟪u, u⟫_ℂ := by
          rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, inner_smul_right]
      _ = _ := by
          have h : ⟪u, u⟫_ℂ = ((‖u‖ ^ 2 : ℝ) : ℂ) := by
            apply Complex.ext
            · simpa using inner_self_eq_norm_sq (𝕜 := ℂ) u
            · simpa using inner_self_im (𝕜 := ℂ) u
          rw [h, ← Complex.ofReal_mul]
  rw [← hint] at hfin
  exact_mod_cast hfin

end ReciprocityTheory.ChartRestriction.DS
