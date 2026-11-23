import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.KinstSecondCountable
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ExpInPPosDef
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PhiFacts

noncomputable section

open MeasureTheory
open scoped ComplexOrder InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section PsiPosAux

open S7

variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}

lemma psiPos_op_inv (T : KType ε Λ) (k : KG ε) :
    T.op k⁻¹ = ContinuousLinearMap.adjoint (T.op k) := by
  simp only [KType.op]
  rw [map_inv, ← ContinuousLinearMap.star_eq_adjoint]
  first
    | rfl
    | (rw [← unitary.star_eq_inv]; rfl)
    | simp

lemma psiPos_inner_P (T : KType ε Λ) (k : KG ε) (v : T.V) :
    ⟪v, (T.op k * projW T * T.op k⁻¹) v⟫_ℂ = ((‖⟪T.op k T.w, v⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
  rw [psiPos_op_inv T k]
  simp only [ContinuousLinearMap.mul_apply, projW, ContinuousLinearMap.smulRight_apply,
    map_smul, inner_smul_right]
  rw [← inner_conj_symm v (T.op k T.w)]
  rw [show ((innerSL ℂ) T.w) (ContinuousLinearMap.adjoint (T.op k) v) = ⟪T.op k T.w, v⟫_ℂ from
    ContinuousLinearMap.adjoint_inner_right _ _ _]
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

lemma psiPos_integral_isPositive (T : KType ε Λ) {c : ℝ} (hc : 0 ≤ c) (g : KG ε → ℝ)
    (hg0 : ∀ k, 0 ≤ g k) :
    ((c : ℂ) • ∫ k, ((g k : ℝ) : ℂ) • (T.op k * projW T * T.op k⁻¹) ∂(muK ε)).IsPositive := by
  set A : T.V →L[ℂ] T.V :=
    (c : ℂ) • ∫ k, ((g k : ℝ) : ℂ) • (T.op k * projW T * T.op k⁻¹) ∂(muK ε) with hA

  have key : ∀ x : T.V, ∃ r : ℝ, 0 ≤ r ∧ ⟪x, A x⟫_ℂ = (r : ℂ) := by
    intro x
    by_cases hint : Integrable (fun k => ((g k : ℝ) : ℂ) • (T.op k * projW T * T.op k⁻¹)) (muK ε)
    · refine ⟨c * ∫ k, g k * ‖⟪T.op k T.w, x⟫_ℂ‖ ^ 2 ∂(muK ε), ?_, ?_⟩
      · exact mul_nonneg hc (integral_nonneg fun k => mul_nonneg (hg0 k) (sq_nonneg _))
      · have hpt : ∀ k, ⟪x, (((g k : ℝ) : ℂ) • (T.op k * projW T * T.op k⁻¹)) x⟫_ℂ =
            ((g k * ‖⟪T.op k T.w, x⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
          intro k
          rw [ContinuousLinearMap.smul_apply, inner_smul_right, psiPos_inner_P, Complex.ofReal_mul]
        rw [hA, ContinuousLinearMap.smul_apply, inner_smul_right,
          ContinuousLinearMap.integral_apply hint x,
          ← integral_inner (hint.apply_continuousLinearMap x)]
        simp_rw [hpt]
        rw [Complex.ofReal_mul]
        first
          | rw [integral_complex_ofReal]
          | exact congrArg _ integral_ofReal
    · refine ⟨0, le_rfl, ?_⟩
      rw [hA, integral_undef hint, smul_zero, ContinuousLinearMap.zero_apply, inner_zero_right,
        Complex.ofReal_zero]
  rw [ContinuousLinearMap.isPositive_iff_complex]
  intro x
  obtain ⟨r, hr, hx⟩ := key x
  have hx' : ⟪A x, x⟫_ℂ = (r : ℂ) := by
    rw [← inner_conj_symm, hx, Complex.conj_ofReal]
  rw [hx']
  refine ⟨?_, ?_⟩
  · simp
  · simpa using hr

lemma psiPos_posDef_conj (k : KG ε) {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) :
    (toMK k⁻¹ * x * toMK k).PosDef := by
  unfold toMK
  have hk : toM (k : UJ ε) ∈ Kset ε := k.2
  unfold Kset at hk
  obtain ⟨hU, -⟩ := hk
  unfold toM at hU ⊢
  have gen' : ∀ U : Matrix (Fin n) (Fin n) ℂ, U ∈ unitary (Matrix (Fin n) (Fin n) ℂ) →
      (star U * x * U).PosDef := by
    intro U hU'
    rw [Matrix.star_eq_conjTranspose]
    apply hx.conjTranspose_mul_mul_same
    apply Matrix.mulVec_injective_iff_isUnit.mpr
    first
      | exact ⟨⟨U, star U, Unitary.mul_star_self_of_mem hU', Unitary.star_mul_self_of_mem hU'⟩, rfl⟩
      | exact ⟨⟨U, star U, unitary.mul_star_self_of_mem hU', unitary.star_mul_self_of_mem hU'⟩, rfl⟩
  have hinv2 : ((((k⁻¹ : KG ε) : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) =
      star ((((k : KG ε) : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) := by
    rw [InvMemClass.coe_inv, InvMemClass.coe_inv]
    apply Units.inv_eq_of_mul_eq_one_left
    first
      | exact Unitary.star_mul_self_of_mem hU
      | exact unitary.star_mul_self_of_mem hU
  rw [hinv2]
  exact gen' _ hU

end PsiPosAux

theorem psi_exp_isPositive {ε : Fin n → Bool} {lam : Fin n → ℝ} (T : S7.KType ε (lowK ε lam))
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)) (μ : Fin n → ℤ) (hμ : S7.IsMu lam μ)
    (hform : ∀ X, inP ε X → Ψ (NormedSpace.exp X) =
      ((Module.finrank ℂ T.V : ℂ) / ((S7.muK ε Set.univ).toReal : ℂ)) •
        ∫ k, S7.PhiM μ (S7.toMK k⁻¹ * NormedSpace.exp X * S7.toMK k)⁻¹ • (T.op k * S7.projW T * T.op k⁻¹)
          ∂(S7.muK ε)) :
    ∀ X, inP ε X → (Ψ (NormedSpace.exp X)).IsPositive := by
  intro X hX
  have hpd : ∀ k : S7.KG ε, (S7.toMK k⁻¹ * NormedSpace.exp X * S7.toMK k)⁻¹.PosDef :=
    fun k => (psiPos_posDef_conj k (S7.exp_noncompactPart_posDef hX)).inv
  let g : S7.KG ε → ℝ := fun k => (S7.PhiM μ (S7.toMK k⁻¹ * NormedSpace.exp X * S7.toMK k)⁻¹).re
  have hphi : ∀ k, S7.PhiM μ (S7.toMK k⁻¹ * NormedSpace.exp X * S7.toMK k)⁻¹ = ((g k : ℝ) : ℂ) := by
    intro k
    apply Complex.ext
    · simp [g]
    · simp [g, (S7.phiM_posDef μ (hpd k)).2]
  have hc : (0 : ℝ) ≤ (Module.finrank ℂ T.V : ℝ) / (S7.muK ε Set.univ).toReal :=
    div_nonneg (Nat.cast_nonneg _) ENNReal.toReal_nonneg
  have hcc : ((Module.finrank ℂ T.V : ℂ) / ((S7.muK ε Set.univ).toReal : ℂ)) =
      ((((Module.finrank ℂ T.V : ℝ) / (S7.muK ε Set.univ).toReal : ℝ)) : ℂ) := by
    push_cast
    rfl
  rw [hform X hX, hcc]
  simp_rw [hphi]
  exact psiPos_integral_isPositive T hc g (fun k => (S7.phiM_posDef μ (hpd k)).1.le)

end ReciprocityTheory.ChartRestriction.DS
