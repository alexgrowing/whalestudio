import Mathlib
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.ClifMod

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

section SlopeTestRemainingChoices

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

private def eD : (V →L[ℂ] ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ V)) where
  toFun ξ := WithLp.toLp 2 fun i => ξ (stdOrthonormalBasis ℂ V i)
  map_add' x y := by ext i; simp
  map_smul' c x := by ext i; simp
  invFun y := ∑ i, y i • innerSL ℂ (stdOrthonormalBasis ℂ V i)
  left_inv ξ := by
    ext v
    have h := (stdOrthonormalBasis ℂ V).sum_repr' v
    conv_rhs => rw [← h]
    simp [ContinuousLinearMap.sum_apply, map_sum, mul_comm]
  right_inv y := by
    ext j
    simp [ContinuousLinearMap.sum_apply, OrthonormalBasis.inner_eq_ite]

private theorem eD_apply (ξ : V →L[ℂ] ℂ) (i) : eD ξ i = ξ (stdOrthonormalBasis ℂ V i) := rfl

private theorem norm_eD (ξ : V →L[ℂ] ℂ) : ‖eD ξ‖ = ‖ξ‖ := by
  set b := stdOrthonormalBasis ℂ V
  set u := (InnerProductSpace.toDual ℂ V).symm ξ
  have hu : ∀ v, ξ v = ⟪u, v⟫_ℂ := fun v => (InnerProductSpace.toDual_symm_apply).symm
  rw [← (InnerProductSpace.toDual ℂ V).symm.norm_map ξ, ← b.repr.norm_map u,
    EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [eD_apply, hu, b.repr_apply_apply, ← inner_conj_symm, Complex.norm_conj]

private def pr (A : V →L[ℂ] V) :
    EuclideanSpace ℂ (Fin (Module.finrank ℂ V)) →L[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ V)) :=
  ((eD (V := V)).toContinuousLinearEquiv : (V →L[ℂ] ℂ) →L[ℂ] _).comp
    (((ContinuousLinearMap.compL ℂ V V ℂ).flip A).comp
      ((eD (V := V)).toContinuousLinearEquiv.symm : _ →L[ℂ] (V →L[ℂ] ℂ)))

private theorem pr_apply (A : V →L[ℂ] V) (y) : pr A y = eD ((eD.symm y).comp A) := rfl

private theorem pr_eD (A : V →L[ℂ] V) (ξ : V →L[ℂ] ℂ) : pr A (eD ξ) = eD (ξ.comp A) := by
  rw [pr_apply, LinearEquiv.symm_apply_apply]

private theorem pr_one : pr (1 : V →L[ℂ] V) = 1 := by
  ext1 y
  rw [pr_apply, ContinuousLinearMap.one_apply]
  show eD ((eD.symm y).comp (ContinuousLinearMap.id ℂ V)) = y
  rw [ContinuousLinearMap.comp_id, LinearEquiv.apply_symm_apply]

private theorem pr_mul (A B : V →L[ℂ] V) : pr (A * B) = pr B * pr A := by
  ext1 y
  rw [ContinuousLinearMap.mul_apply, pr_apply, pr_apply, pr_apply, LinearEquiv.symm_apply_apply,
    ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc]

private theorem continuous_pr : Continuous (pr (V := V)) := by
  unfold pr
  fun_prop

private theorem trace_pr (A : V →L[ℂ] V) :
    LinearMap.trace ℂ (EuclideanSpace ℂ (Fin (Module.finrank ℂ V)))
      ((pr A : EuclideanSpace ℂ (Fin (Module.finrank ℂ V)) →L[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ V))) :
        EuclideanSpace ℂ (Fin (Module.finrank ℂ V)) →ₗ[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ V))) =
      LinearMap.trace ℂ V (A : V →ₗ[ℂ] V) := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (EuclideanSpace.basisFun (Fin (Module.finrank ℂ V)) ℂ).toBasis,
    LinearMap.trace_eq_matrix_trace ℂ (stdOrthonormalBasis ℂ V).toBasis]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.coe_toBasis, OrthonormalBasis.repr_apply_apply,
    EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr, ContinuousLinearMap.coe_coe, pr_apply, eD_apply]
  rw [EuclideanSpace.inner_single_left, map_one, one_mul, eD_apply, ContinuousLinearMap.comp_apply]
  show (∑ j, (EuclideanSpace.single i (1 : ℂ)) j • innerSL ℂ (stdOrthonormalBasis ℂ V j))
    (A (stdOrthonormalBasis ℂ V i)) = _
  simp [ContinuousLinearMap.sum_apply, EuclideanSpace.single_apply]

end SlopeTestRemainingChoices

theorem UpperTheory.RealTr.dualEx :
    ∀ (n : ℕ) (E : KMod n) (T : E.V →L[ℂ] E.V), (∀ k, T * E.ρ k = E.ρ k * T) → ∃ (E' : KMod n) (e : (E.V →L[ℂ] ℂ) ≃ₗ[ℂ] E'.V) (T' : Module.End ℂ E'.V),
      (∀ k ξ, e (ξ ∘L E.ρ k⁻¹) = E'.ρ k (e ξ)) ∧ (∀ ξ, e (dualT E T ξ) = T' (e ξ)) ∧
      ∀ k, LinearMap.trace ℂ E'.V (E'.ρ k : E'.V →ₗ[ℂ] E'.V) = LinearMap.trace ℂ E.V (E.ρ k⁻¹ : E.V →ₗ[ℂ] E.V) ∧
        LinearMap.trace ℂ E'.V ((E'.ρ k : E'.V →ₗ[ℂ] E'.V) * T') = LinearMap.trace ℂ E.V ((E.ρ k⁻¹ * T : E.V →L[ℂ] E.V) : E.V →ₗ[ℂ] E.V) := by
  intro n E T hT
  have hnorm : ∀ (k : UK n) (ξ : E.V →L[ℂ] ℂ), ‖ξ.comp (E.ρ k)‖ ≤ ‖ξ‖ := by
    intro k ξ
    have hk : ‖E.ρ k‖ ≤ 1 :=
      ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by rw [E.iso, one_mul]
    calc ‖ξ.comp (E.ρ k)‖ ≤ ‖ξ‖ * ‖E.ρ k‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖ξ‖ * 1 := by gcongr
      _ = ‖ξ‖ := mul_one _
  have hinv : Continuous (fun k : UK n => k⁻¹) := by
    first
    | exact continuous_inv
    | exact Continuous.subtype_mk (continuous_star.comp continuous_subtype_val) _
  let ρ' : UK n →* (EuclideanSpace ℂ (Fin (Module.finrank ℂ E.V)) →L[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ E.V))) :=
    { toFun := fun k => pr (E.ρ k⁻¹)
      map_one' := by simp [pr_one]
      map_mul' := by
        intro k l
        simp only [_root_.mul_inv_rev, map_mul, pr_mul] }
  let E' : KMod n :=
    { V := EuclideanSpace ℂ (Fin (Module.finrank ℂ E.V))
      ρ := ρ'
      iso := by
        intro k y
        obtain ⟨ξ, rfl⟩ := eD.surjective y
        show ‖pr (E.ρ k⁻¹) (eD ξ)‖ = ‖eD ξ‖
        rw [pr_eD, norm_eD, norm_eD]
        apply le_antisymm (hnorm _ ξ)
        calc ‖ξ‖ = ‖(ξ.comp (E.ρ k⁻¹)).comp (E.ρ k)‖ := by
              rw [ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.mul_def, ← map_mul, inv_mul_cancel,
                map_one, ContinuousLinearMap.one_def, ContinuousLinearMap.comp_id]
          _ ≤ ‖ξ.comp (E.ρ k⁻¹)‖ := hnorm _ _
      cont := continuous_pr.comp (E.cont.comp hinv) }
  refine ⟨E', eD, (pr T : E'.V →L[ℂ] E'.V), ?_, ?_, ?_⟩
  · intro k ξ
    exact (pr_eD _ ξ).symm
  · intro ξ
    exact (pr_eD T ξ).symm
  · intro k
    constructor
    · exact trace_pr (E.ρ k⁻¹)
    · show LinearMap.trace ℂ _ ((pr (E.ρ k⁻¹) : E'.V →ₗ[ℂ] E'.V) * (pr T : E'.V →ₗ[ℂ] E'.V)) = _
      rw [← ContinuousLinearMap.coe_mul, ← pr_mul, trace_pr, hT]
