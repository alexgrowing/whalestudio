import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.KFacts
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PhiFacts
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.DTauFacts

noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}

private lemma toMatrix_mul_alt (a b : KG ε) : toMK (a * b) = toMK a * toMK b := rfl

private lemma toMatrix_one_alt : toMK (1 : KG ε) = 1 := rfl

private lemma toMatrix_inv_mul (a : KG ε) : toMK a⁻¹ * toMK a = 1 := by
  rw [← toMatrix_mul_alt, inv_mul_cancel, toMatrix_one_alt]

private lemma toMatrix_mul_inv (a : KG ε) : toMK a * toMK a⁻¹ = 1 := by
  rw [← toMatrix_mul_alt, mul_inv_cancel, toMatrix_one_alt]

private lemma kType_op_mul (T : KType ε Λ) (a b : KG ε) : T.op (a * b) = T.op a * T.op b := by
  unfold KType.op
  rw [map_mul]
  rfl

private lemma kType_op_one (T : KType ε Λ) : T.op 1 = 1 := by
  unfold KType.op
  rw [map_one]
  rfl

private lemma kType_op_mul_inv (T : KType ε Λ) (a : KG ε) : T.op a * T.op a⁻¹ = 1 := by
  rw [← kType_op_mul, mul_inv_cancel, kType_op_one]

private lemma kType_op_inv_mul (T : KType ε Λ) (a : KG ε) : T.op a⁻¹ * T.op a = 1 := by
  rw [← kType_op_mul, inv_mul_cancel, kType_op_one]

private def ps2E (T : KType ε Λ) (k : KG ε) : T.V ≃L[ℂ] T.V :=
  ContinuousLinearEquiv.equivOfInverse (T.op k) (T.op k⁻¹)
    (fun v => by
      have := congrArg (fun A : T.V →L[ℂ] T.V => A v) (kType_op_inv_mul T k)
      simpa using this)
    (fun v => by
      have := congrArg (fun A : T.V →L[ℂ] T.V => A v) (kType_op_mul_inv T k)
      simpa using this)

private def ps2C (T : KType ε Λ) (k : KG ε) : (T.V →L[ℂ] T.V) ≃L[ℂ] (T.V →L[ℂ] T.V) :=
  (ps2E T k).arrowCongr (ps2E T k)

private lemma conjAction_apply (T : KType ε Λ) (k : KG ε) (A : T.V →L[ℂ] T.V) :
    ps2C T k A = T.op k * A * T.op k⁻¹ := by
  ext v
  rfl

private lemma kType_schur_lemma (T : KType ε Λ) (A : T.V →L[ℂ] T.V) (hA : ∀ k, T.op k * A = A * T.op k) :
    ∃ c : ℂ, A = c • (1 : T.V →L[ℂ] T.V) := by
  have hw : T.w ≠ 0 := fun h => by
    have := T.w_norm
    rw [h, norm_zero] at this
    exact zero_ne_one this
  haveI : Nontrivial T.V := ⟨⟨T.w, 0, hw⟩⟩
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (A : Module.End ℂ T.V)
  refine ⟨c, ?_⟩
  have key : ∀ k v, A (T.op k v) = T.op k (A v) := fun k v => by
    have := congrArg (fun B : T.V →L[ℂ] T.V => B v) (hA k)
    simp only [ContinuousLinearMap.mul_apply] at this
    exact this.symm
  have hinv : ∀ k : KG ε, ∀ v ∈ Module.End.eigenspace (A : Module.End ℂ T.V) c,
      ((T.τ k : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) v ∈
        Module.End.eigenspace (A : Module.End ℂ T.V) c := by
    intro k v hv
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    change A (T.op k v) = c • T.op k v
    rw [key, show A v = c • v from hv, map_smul]
  rcases T.irred _ hinv with h | h
  · exfalso
    obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
    have hv1 : v ∈ Module.End.eigenspace (A : Module.End ℂ T.V) c := by
      rw [Module.End.mem_eigenspace_iff]
      exact hv.apply_eq_smul
    rw [h] at hv1
    exact hv.2 ((Submodule.mem_bot ℂ).1 hv1)
  · ext v
    have hv : v ∈ Module.End.eigenspace (A : Module.End ℂ T.V) c := by
      rw [h]
      exact Submodule.mem_top
    rw [Module.End.mem_eigenspace_iff] at hv
    simpa using hv

private lemma continuous_kType_op (T : KType ε Λ) : Continuous fun k : KG ε => T.op k := continuous_subtype_val.comp T.cont

private lemma continuous_conj_projection (T : KType ε Λ) :
    Continuous fun k : KG ε => T.op k * projW T * T.op k⁻¹ := ((continuous_kType_op T).mul continuous_const).mul ((continuous_kType_op T).comp continuous_inv)

private lemma integral_conj_equivariant (T : KType ε Λ) (μ : Fin n → ℤ) (k : KG ε) (x : Matrix (Fin n) (Fin n) ℂ) :
    ∫ k', PhiM μ (toMK k'⁻¹ * (toMK k * x * toMK k⁻¹) * toMK k') • (T.op k' * projW T * T.op k'⁻¹) ∂(muK ε) =
      ps2C T k (∫ k', PhiM μ (toMK k'⁻¹ * x * toMK k') • (T.op k' * projW T * T.op k'⁻¹) ∂(muK ε)) := by
  haveI : (muK ε).IsMulLeftInvariant := by
    unfold muK
    infer_instance
  rw [← ContinuousLinearEquiv.integral_comp_comm (ps2C T k)]
  calc _ = ∫ k', PhiM μ (toMK (k * k')⁻¹ * (toMK k * x * toMK k⁻¹) * toMK (k * k')) •
        (T.op (k * k') * projW T * T.op (k * k')⁻¹) ∂(muK ε) :=
        (MeasureTheory.integral_mul_left_eq_self (fun k' => PhiM μ (toMK k'⁻¹ * (toMK k * x * toMK k⁻¹) *
          toMK k') • (T.op k' * projW T * T.op k'⁻¹)) k).symm
    _ = _ := by
        congr 1
        funext k'
        rw [map_smul, conjAction_apply]
        congr 1
        · congr 1
          rw [_root_.mul_inv_rev, toMatrix_mul_alt, toMatrix_mul_alt]
          calc _ = toMK k'⁻¹ * (toMK k⁻¹ * toMK k) * x * (toMK k⁻¹ * toMK k) * toMK k' := by
                simp only [Matrix.mul_assoc]
            _ = _ := by rw [toMatrix_inv_mul, Matrix.mul_one, Matrix.mul_one]
        · rw [_root_.mul_inv_rev, kType_op_mul, kType_op_mul]
          simp only [mul_assoc]

theorem psM_conj (T : KType ε Λ) (μ : Fin n → ℤ) (k : KG ε) (x : Matrix (Fin n) (Fin n) ℂ) :
    psM T μ (toMK k * x * toMK k⁻¹) = T.op k * psM T μ x * T.op k⁻¹ := by
  simp only [psM]
  rw [integral_conj_equivariant, conjAction_apply, mul_smul_comm, smul_mul_assoc]

theorem psM_one (T : KType ε Λ) (μ : Fin n → ℤ) : psM T μ 1 = 1 := by
  have hw : T.w ≠ 0 := fun h => by
    have := T.w_norm
    rw [h, norm_zero] at this
    exact zero_ne_one this
  haveI : Nontrivial T.V := ⟨⟨T.w, 0, hw⟩⟩
  haveI : CompactSpace (KG ε) := compactSpace_KG ε
  haveI : IsFiniteMeasureOnCompacts (muK ε) := by
    unfold muK
    infer_instance
  have hPhi1 : PhiM μ (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
    unfold PhiM
    refine Finset.prod_eq_one fun i _ => ?_
    unfold lead
    rw [dif_pos (by have := i.isLt; omega), Matrix.submatrix_one _ (Fin.castLE_injective _),
      Matrix.det_one, _root_.one_zpow]
  have hcomm : ∀ k : KG ε, T.op k * psM T μ 1 = psM T μ 1 * T.op k := by
    intro k
    have h := psM_conj T μ k 1
    rw [Matrix.mul_one, toMatrix_mul_inv] at h
    calc T.op k * psM T μ 1 = T.op k * psM T μ 1 * (T.op k⁻¹ * T.op k) := by
          rw [kType_op_inv_mul, mul_one]
      _ = T.op k * psM T μ 1 * T.op k⁻¹ * T.op k := by simp only [mul_assoc]
      _ = psM T μ 1 * T.op k := by rw [← h]
  obtain ⟨c, hc⟩ := kType_schur_lemma T (psM T μ 1) hcomm
  obtain ⟨tr, htr⟩ : ∃ tr : (T.V →L[ℂ] T.V) →L[ℂ] ℂ,
      ∀ A, tr A = LinearMap.trace ℂ T.V (A : T.V →ₗ[ℂ] T.V) :=
    ⟨LinearMap.toContinuousLinearMap ((LinearMap.trace ℂ T.V).comp (ContinuousLinearMap.coeLM ℂ)),
      fun A => rfl⟩
  have hP : LinearMap.trace ℂ T.V (projW T : T.V →ₗ[ℂ] T.V) = 1 := by
    have e2 : (projW T : T.V →ₗ[ℂ] T.V) =
        ((innerSL ℂ T.w : T.V →L[ℂ] ℂ) : T.V →ₗ[ℂ] ℂ).smulRight T.w := LinearMap.ext fun v => rfl
    rw [e2, LinearMap.trace_smulRight]
    simp [inner_self_eq_norm_sq_to_K, T.w_norm]
  have htrk : ∀ k, tr (T.op k * projW T * T.op k⁻¹) = 1 := by
    intro k
    rw [htr]
    have e1 : ((T.op k * projW T * T.op k⁻¹ : T.V →L[ℂ] T.V) : T.V →ₗ[ℂ] T.V) =
        (ps2E T k).toLinearEquiv.conj (projW T : T.V →ₗ[ℂ] T.V) := LinearMap.ext fun v => rfl
    rw [e1, LinearMap.trace_conj', hP]
  have hint : Integrable (fun k : KG ε => T.op k * projW T * T.op k⁻¹) (muK ε) :=
    (continuous_conj_projection T).integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (Set.subset_univ _))
  have hv : ((muK ε Set.univ).toReal : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (muK_univ_pos ε).ne'
  have hd : (Module.finrank ℂ T.V : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have h1 : tr (psM T μ 1) = c * (Module.finrank ℂ T.V : ℂ) := by
    rw [htr, hc]
    simp [LinearMap.trace_one]
  have hI : psM T μ 1 = ((Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ)) •
      ∫ k, (T.op k * projW T * T.op k⁻¹) ∂(muK ε) := by
    simp only [psM]
    congr 1
    congr 1
    funext k
    rw [Matrix.mul_one, toMatrix_inv_mul, hPhi1, one_smul]
  have h2 : tr (psM T μ 1) = (Module.finrank ℂ T.V : ℂ) := by
    rw [hI, map_smul, ← ContinuousLinearMap.integral_comp_comm tr hint]
    simp only [htrk, integral_const, smul_eq_mul, Complex.real_smul, mul_one]
    exact div_mul_cancel₀ _ hv
  have hc1 : c = 1 := by
    have := h1.symm.trans h2
    exact mul_right_cancel₀ hd (this.trans (one_mul _).symm)
  rw [hc, hc1, one_smul]

private def ps2J (ε : Fin n → Bool) : KG ε :=
  ⟨⟨⟨Jm ε, Jm ε, Jm_mul_self ε, Jm_mul_self ε⟩, by
      show (Jm ε)ᴴ * Jm ε * Jm ε = Jm ε
      rw [Jm_conjTranspose, Jm_mul_self, Matrix.one_mul]⟩,
    by
      show Jm ε ∈ Kset ε
      refine ⟨?_, rfl⟩
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Jm_conjTranspose, Jm_mul_self]⟩

private lemma toMatrix_signElement : toMK (ps2J ε) = Jm ε := rfl

private lemma signElement_inv : (ps2J ε)⁻¹ = ps2J ε := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  show Jm ε * Jm ε = 1
  exact Jm_mul_self ε

private lemma signElement_central (k : KG ε) : ps2J ε * k = k * ps2J ε := by
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  show Jm ε * toMK k = toMK k * Jm ε
  exact (show toMK k ∈ Kset ε from k.2).2.symm

theorem psM_exp_neg (T : KType ε Λ) (μ : Fin n → ℤ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) :
    psM T μ (NormedSpace.exp (-X)) = psM T μ (NormedSpace.exp X) := by
  have hJ : Jm ε * X * Jm ε = -X := by
    calc Jm ε * X * Jm ε = Jm ε * (X * Jm ε) := Matrix.mul_assoc _ _ _
      _ = Jm ε * -(Jm ε * X) := by rw [hX.2]
      _ = -X := by rw [Matrix.mul_neg, ← Matrix.mul_assoc, Jm_mul_self, Matrix.one_mul]
  have hinv : (Jm ε)⁻¹ = Jm ε := Matrix.inv_eq_left_inv (Jm_mul_self ε)
  have hU : IsUnit (Jm ε) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_left_inverse (Jm_mul_self ε))
  have hE := Matrix.exp_conj (Jm ε) X hU
  rw [hinv, hJ] at hE
  have hE' : NormedSpace.exp (-X) = toMK (ps2J ε) * NormedSpace.exp X * toMK (ps2J ε)⁻¹ := by
    rw [signElement_inv, toMatrix_signElement]
    exact hE
  rw [hE', psM_conj]
  obtain ⟨c, hc⟩ := kType_schur_lemma T (T.op (ps2J ε)) (fun k => by
    rw [← kType_op_mul, ← kType_op_mul, signElement_central])
  have hm := kType_op_mul_inv T (ps2J ε)
  rw [hc] at hm ⊢
  calc c • (1 : T.V →L[ℂ] T.V) * psM T μ (NormedSpace.exp X) * T.op (ps2J ε)⁻¹ =
        psM T μ (NormedSpace.exp X) * (c • (1 : T.V →L[ℂ] T.V) * T.op (ps2J ε)⁻¹) := by
        simp only [smul_mul_assoc, one_mul, mul_smul_comm]
    _ = psM T μ (NormedSpace.exp X) := by rw [hm, mul_one]

end ReciprocityTheory.ChartRestriction.DS.S7
