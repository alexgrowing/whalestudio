import Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.HlamStable
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.KSchur
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.DecPos
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PhiFacts
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.SumNormAdjointSqEqHsOp

noncomputable section

open Finset MeasureTheory Matrix
open scoped InnerProductSpace ComplexOrder

namespace GlobalTheory.CompanionTheory.HsPsProof

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7 PositivityTheory.RgFd

section General

variable {K V : Type*} [TopologicalSpace K] [T2Space K] [CompactSpace K] [SecondCountableTopology K]
  [MeasurableSpace K] [BorelSpace K] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteDimensional ℂ V] [CompleteSpace V]

theorem hsOp_integral_rank_one (m : Measure K) [IsFiniteMeasure m] {u : K → V} (hu : Continuous u)
    {φ : K → ℝ} (hφ : Continuous φ) {P : K → V →L[ℂ] V} (hPc : Continuous P)
    (hP : ∀ k b, P k b = ⟪u k, b⟫_ℂ • u k) (d : ℝ) :
    hsOp ((d : ℂ) • ∫ k, ((φ k : ℝ) : ℂ) • P k ∂m) =
      d ^ 2 * ∫ p, φ p.1 * φ p.2 * ‖⟪u p.1, u p.2⟫_ℂ‖ ^ 2 ∂(m.prod m) := by
  have hφC : Continuous fun k => ((φ k : ℝ) : ℂ) := Complex.continuous_ofReal.comp hφ
  have hInt : Integrable (fun k => ((φ k : ℝ) : ℂ) • P k) m :=
    (integrableOn_univ).mp ((hφC.smul hPc).continuousOn.integrableOn_compact isCompact_univ)
  set A : V →L[ℂ] V := (d : ℂ) • ∫ k, ((φ k : ℝ) : ℂ) • P k ∂m with hA
  have hkey : ∀ y x : V, ⟪y, A x⟫_ℂ =
      (d : ℂ) * ∫ k, ((φ k : ℝ) : ℂ) * (⟪u k, x⟫_ℂ * ⟪y, u k⟫_ℂ) ∂m := by
    intro y x
    have hIx : Integrable (fun k => (((φ k : ℝ) : ℂ) • P k) x) m :=
      (ContinuousLinearMap.apply ℂ V x).integrable_comp hInt
    rw [hA, _root_.smul_apply, inner_smul_right, ContinuousLinearMap.integral_apply hInt,
      ← integral_inner hIx]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only [_root_.smul_apply, inner_smul_right, hP]
  have hQ : ∀ v : V, ⟪v, A v⟫_ℂ = ((d * ∫ k, φ k * ‖⟪v, u k⟫_ℂ‖ ^ 2 ∂m : ℝ) : ℂ) := by
    intro v
    rw [hkey]
    have : ∀ k, ((φ k : ℝ) : ℂ) * (⟪u k, v⟫_ℂ * ⟪v, u k⟫_ℂ) =
        ((φ k * ‖⟪v, u k⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
      intro k
      rw [← inner_conj_symm (u k) v, Complex.conj_mul']
      push_cast; ring
    simp_rw [this]
    rw [integral_complex_ofReal]
    push_cast; ring
  have hQ' : ∀ v : V, ⟪A v, v⟫_ℂ = ((d * ∫ k, φ k * ‖⟪v, u k⟫_ℂ‖ ^ 2 ∂m : ℝ) : ℂ) := by
    intro v
    rw [← inner_conj_symm, hQ, Complex.conj_ofReal]
  set b := stdOrthonormalBasis ℂ V with hb
  have hsum : ∀ v : V, ∑ i, ⟪v, b i⟫_ℂ * ⟪A (b i), v⟫_ℂ = ⟪A v, v⟫_ℂ := by
    intro v
    simp_rw [← ContinuousLinearMap.adjoint_inner_right]
    rw [b.sum_inner_mul_inner]
  have hterm : ∀ i, ((‖A (b i)‖ ^ 2 : ℝ) : ℂ) =
      (d : ℂ) * ∫ k, ((φ k : ℝ) : ℂ) * (⟪u k, b i⟫_ℂ * ⟪A (b i), u k⟫_ℂ) ∂m := by
    intro i
    rw [← hkey, inner_self_eq_norm_sq_to_K]
    push_cast; rfl
  have hintg : ∀ i ∈ (Finset.univ : Finset _), Integrable
      (fun k => ((φ k : ℝ) : ℂ) * (⟪u k, b i⟫_ℂ * ⟪A (b i), u k⟫_ℂ)) m := by
    intro i _
    have hc : Continuous fun k => ((φ k : ℝ) : ℂ) * (⟪u k, b i⟫_ℂ * ⟪A (b i), u k⟫_ℂ) :=
      hφC.mul ((hu.inner continuous_const).mul (continuous_const.inner hu))
    exact (integrableOn_univ).mp (hc.continuousOn.integrableOn_compact isCompact_univ)
  have hC : ((hsOp A : ℝ) : ℂ) =
      ((d * ∫ k, φ k * (d * ∫ k', φ k' * ‖⟪u k, u k'⟫_ℂ‖ ^ 2 ∂m) ∂m : ℝ) : ℂ) := by
    calc ((hsOp A : ℝ) : ℂ) = ∑ i, ((‖A (b i)‖ ^ 2 : ℝ) : ℂ) := by
          simp only [hsOp, hb]; push_cast; rfl
      _ = ∑ i, (d : ℂ) * ∫ k, ((φ k : ℝ) : ℂ) * (⟪u k, b i⟫_ℂ * ⟪A (b i), u k⟫_ℂ) ∂m :=
          sum_congr rfl fun i _ => hterm i
      _ = (d : ℂ) * ∫ k, ∑ i, ((φ k : ℝ) : ℂ) * (⟪u k, b i⟫_ℂ * ⟪A (b i), u k⟫_ℂ) ∂m := by
          rw [← mul_sum, integral_finset_sum _ hintg]
      _ = (d : ℂ) * ∫ k, ((φ k * (d * ∫ k', φ k' * ‖⟪u k, u k'⟫_ℂ‖ ^ 2 ∂m) : ℝ) : ℂ) ∂m := by
          congr 1
          refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
          simp only []
          rw [← mul_sum, hsum, hQ']
          push_cast; rfl
      _ = ((d * ∫ k, φ k * (d * ∫ k', φ k' * ‖⟪u k, u k'⟫_ℂ‖ ^ 2 ∂m) ∂m : ℝ) : ℂ) := by
          rw [integral_complex_ofReal]
          push_cast; rfl
  have hR : hsOp A = d * ∫ k, φ k * (d * ∫ k', φ k' * ‖⟪u k, u k'⟫_ℂ‖ ^ 2 ∂m) ∂m := by
    exact_mod_cast hC
  have hF : Continuous fun p : K × K => φ p.1 * φ p.2 * ‖⟪u p.1, u p.2⟫_ℂ‖ ^ 2 :=
    ((hφ.comp continuous_fst).mul (hφ.comp continuous_snd)).mul
      (((hu.comp continuous_fst).inner (hu.comp continuous_snd)).norm.pow 2)
  have hFi : Integrable (fun p : K × K => φ p.1 * φ p.2 * ‖⟪u p.1, u p.2⟫_ℂ‖ ^ 2) (m.prod m) :=
    (integrableOn_univ).mp (hF.continuousOn.integrableOn_compact isCompact_univ)
  rw [hR, integral_prod _ hFi]
  have e1 : ∀ k, ∫ k', φ k * φ k' * ‖⟪u k, u k'⟫_ℂ‖ ^ 2 ∂m =
      φ k * ∫ k', φ k' * ‖⟪u k, u k'⟫_ℂ‖ ^ 2 ∂m := by
    intro k
    rw [← integral_const_mul]
    simp only [mul_assoc]
  have e2 : ∀ k, φ k * (d * ∫ k', φ k' * ‖⟪u k, u k'⟫_ℂ‖ ^ 2 ∂m) =
      d * (φ k * ∫ k', φ k' * ‖⟪u k, u k'⟫_ℂ‖ ^ 2 ∂m) := fun k => by ring
  simp_rw [e1, e2]
  rw [integral_const_mul]
  ring

end General

variable {n : ℕ} {ε : Fin n → Bool}

private lemma posDef_conj (k : KG ε) {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) :
    (toMK k⁻¹ * x * toMK k).PosDef := by
  rw [toMK_inv]
  refine hx.conjTranspose_mul_mul_same ?_
  intro a b hab
  have h := congrArg (fun y => (toMK k)ᴴ.mulVec y) hab
  simpa only [Matrix.mulVec_mulVec, (toMK_facts k).1, Matrix.one_mulVec] using h

private lemma cont_phiK (μ : Fin n → ℤ) {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) :
    Continuous (phiK μ x : KG ε → ℝ) := by
  have hm : Continuous (fun k : KG ε => toMK k) :=
    (continuous_toM ε).comp continuous_subtype_val
  have hz : Continuous (fun k : KG ε => toMK k⁻¹ * x * toMK k) :=
    ((hm.comp continuous_inv).mul continuous_const).mul hm
  refine Complex.continuous_re.comp ?_
  exact (phiM_differentiableOn μ).continuousOn.comp_continuous hz
    (fun k => posSet_subset_omega (posDef_conj k hx))

private lemma cK_mul {Λ : Fin n → ℝ} (T : KType ε Λ) (a b : KG ε) :
    cK T (a⁻¹ * b) = ‖⟪T.op a T.w, T.op b T.w⟫_ℂ‖ := by
  rw [cK, CompactHaarProbability.op_mul, KType_op_inv_eq_adjoint, ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.adjoint_inner_right]

theorem hsPs : HsPs := by
  intro n ε Λ T μ x hx
  have hφc : Continuous (phiK μ x : KG ε → ℝ) := cont_phiK μ hx
  have hφeq : ∀ k : KG ε, PhiM μ (toMK k⁻¹ * x * toMK k) = ((phiK μ x k : ℝ) : ℂ) := fun k =>
    Complex.ext (by simp [phiK]) (by simp [(phiM_posDef μ (posDef_conj k hx)).2])
  have hps : psM T μ x = ((Module.finrank ℂ T.V : ℝ) : ℂ) •
      ∫ k, ((phiK μ x k : ℝ) : ℂ) • (T.op k * projW T * T.op k⁻¹) ∂(dk ε) := by
    unfold psM dk
    simp_rw [hφeq]
    rw [integral_smul_measure, ENNReal.toReal_inv, ← Complex.coe_smul, smul_smul]
    congr 1
    push_cast
    ring
  have hu : Continuous fun k : KG ε => T.op k T.w :=
    (KType_continuous_op T).clm_apply continuous_const
  have hPc : Continuous fun k : KG ε => T.op k * projW T * T.op k⁻¹ :=
    ((KType_continuous_op T).mul continuous_const).mul ((KType_continuous_op T).comp continuous_inv)
  rw [hps, hsOp_integral_rank_one (dk ε) hu hφc hPc (conj_projection_apply T)]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only [hI, cK_mul]

end GlobalTheory.CompanionTheory.HsPsProof
