import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormEvalLeSumNormCoeff
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

noncomputable section
open MeasureTheory Topology Matrix

namespace GlobalTheory.InvFormBdd

theorem exists_form_of_bounded {ι : Type} [Fintype ι] [DecidableEq ι]
    (H : Subgroup (Matrix.GeneralLinearGroup ι ℂ)) (C : ℝ)
    (hC : ∀ h ∈ H, ∀ i j, ‖(h : Matrix ι ι ℂ) i j‖ ≤ C) :
    ∃ β : (ι → ℂ) →ₗ⋆[ℂ] (ι → ℂ) →ₗ[ℂ] ℂ, (∀ x y, β x y = starRingEnd ℂ (β y x)) ∧
      (∀ x, x ≠ 0 → 0 < (β x x).re) ∧
      ∀ h ∈ H, ∀ x y, β ((h : Matrix ι ι ℂ) *ᵥ x) ((h : Matrix ι ι ℂ) *ᵥ y) = β x y := by
  classical
  let A : Set (Matrix ι ι ℂ) := Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Metric.closedBall (0:ℂ) C
  have hA : IsCompact A := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  let S : Set (Matrix.GeneralLinearGroup ι ℂ) :=
    Units.embedProduct (Matrix ι ι ℂ) ⁻¹' (A ×ˢ (MulOpposite.op '' A))
  have hS : IsCompact S := Units.isClosedEmbedding_embedProduct.isCompact_preimage
    (hA.prod (hA.image MulOpposite.continuous_op))
  have hHS : (H : Set (Matrix.GeneralLinearGroup ι ℂ)) ⊆ S := by
    intro h hh
    refine ⟨fun i _ j _ => ?_, ⟨(h⁻¹ : Matrix.GeneralLinearGroup ι ℂ).val, fun i _ j _ => ?_, rfl⟩⟩
    · simpa using hC h hh i j
    · simpa using hC _ (H.inv_mem hh) i j
  let K := H.topologicalClosure
  have hK : IsCompact (K : Set (Matrix.GeneralLinearGroup ι ℂ)) :=
    hS.of_isClosed_subset H.isClosed_topologicalClosure (closure_minimal hHS hS.isClosed)
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  letI : MeasurableSpace K := borel K
  haveI : BorelSpace K := ⟨rfl⟩
  let μ : Measure K := Measure.haar
  let N : K → Matrix ι ι ℂ := fun k => ((k⁻¹ : K) : Matrix.GeneralLinearGroup ι ℂ).val
  have hN : Continuous N := Units.continuous_val.comp (continuous_subtype_val.comp continuous_inv)
  let φ : K → (ι → ℂ) → (ι → ℂ) → ℂ := fun k x y => star (N k *ᵥ x) ⬝ᵥ (N k *ᵥ y)
  have hφc : ∀ x y, Continuous fun k => φ k x y := by
    intro x y
    have h1 : Continuous fun k => N k *ᵥ x := hN.matrix_mulVec continuous_const
    have h2 : Continuous fun k => N k *ᵥ y := hN.matrix_mulVec continuous_const
    exact (continuous_star.comp h1).dotProduct h2
  have hφi : ∀ x y, Integrable (fun k => φ k x y) μ := fun x y =>
    (hφc x y).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let β : (ι → ℂ) →ₗ⋆[ℂ] (ι → ℂ) →ₗ[ℂ] ℂ := LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ)
    (fun x y => ∫ k, φ k x y ∂μ)
    (fun x x' y => by
      rw [← integral_add (hφi x y) (hφi x' y)]
      congr 1; funext k; simp [φ, Matrix.mulVec_add, add_dotProduct])
    (fun c x y => by
      rw [smul_eq_mul, ← integral_const_mul]
      congr 1; funext k; simp [φ, Matrix.mulVec_smul, smul_dotProduct])
    (fun x y y' => by
      rw [← integral_add (hφi x y) (hφi x y')]
      congr 1; funext k; simp [φ, Matrix.mulVec_add, dotProduct_add])
    (fun c x y => by
      rw [RingHom.id_apply, smul_eq_mul, ← integral_const_mul]
      congr 1; funext k; simp [φ, Matrix.mulVec_smul, dotProduct_smul])
  refine ⟨β, fun x y => ?_, fun x hx => ?_, fun h hh x y => ?_⟩
  · show ∫ k, φ k x y ∂μ = starRingEnd ℂ (∫ k, φ k y x ∂μ)
    rw [← integral_conj]
    congr 1; funext k
    simp [φ, dotProduct, map_sum, mul_comm]
  · show 0 < (∫ k, φ k x x ∂μ).re
    have e := integral_re (hφi x x)
    simp only [RCLike.re_to_complex] at e
    rw [← e]
    have hre : ∀ k, (φ k x x).re = ∑ i, ‖(N k *ᵥ x) i‖ ^ 2 := by
      intro k
      simp only [φ, dotProduct, Pi.star_apply, Complex.re_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Complex.star_def, Complex.conj_mul']
      norm_cast
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1)
      (Complex.continuous_re.comp (hφc x x)) (HasCompactSupport.of_compactSpace _) ?_ ?_
    · intro k
      simp only [Pi.zero_apply, Function.comp_apply, hre]
      exact Finset.sum_nonneg fun i _ => sq_nonneg _
    · simp only [Function.comp_apply, hre]
      have hN1 : N 1 = 1 := by simp [N]
      rw [hN1, Matrix.one_mulVec]
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
      refine ne_of_gt (Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨i, Finset.mem_univ _, ?_⟩)
      have : x i ≠ 0 := hi
      positivity
  · show ∫ k, φ k ((h : Matrix ι ι ℂ) *ᵥ x) ((h : Matrix ι ι ℂ) *ᵥ y) ∂μ = ∫ k, φ k x y ∂μ
    have hhK : h ∈ K := H.le_topologicalClosure hh
    rw [← integral_mul_left_eq_self (μ := μ) (fun k => φ k x y) (⟨h, hhK⟩⁻¹ : K)]
    congr 1; funext k
    simp only [φ, N, _root_.mul_inv_rev, inv_inv, Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec]

end GlobalTheory.InvFormBdd

noncomputable section
open MeasureTheory Topology Matrix

namespace GlobalTheory.InvFormBdd

theorem norm_eval_le {σ : Type} (P : MvPolynomial σ ℂ) (v : σ → ℂ) (hv : ∀ s, ‖v s‖ ≤ 1) :
    ‖MvPolynomial.eval v P‖ ≤ ∑ d ∈ P.support, ‖MvPolynomial.coeff d P‖ := by
  first
  | exact @_root_.GlobalTheory.EvalNormCoefficientBound.norm_eval_le_sum_norm_coeff
  | exact _root_.GlobalTheory.EvalNormCoefficientBound.norm_eval_le_sum_norm_coeff
  | (apply _root_.GlobalTheory.EvalNormCoefficientBound.norm_eval_le_sum_norm_coeff <;> assumption)
  | (intros; apply _root_.GlobalTheory.EvalNormCoefficientBound.norm_eval_le_sum_norm_coeff <;> assumption)
  | (intros; apply @_root_.GlobalTheory.EvalNormCoefficientBound.norm_eval_le_sum_norm_coeff <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.EvalNormCoefficientBound.norm_eval_le_sum_norm_coeff ..)

theorem norm_emb_le_one {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin n) L) (hg : g ∈ GQ0 L n) (τ : L →+* ℂ) (i j : Fin n) :
    ‖τ ((g : Matrix (Fin n) (Fin n) L) i j)‖ ≤ 1 := by
  have h1 : (g : Matrix (Fin n) (Fin n) L) * conjT (IsCMField.complexConj L : L →+* L) (g : Matrix (Fin n) (Fin n) L) = 1 := hg
  have h2 := congrFun (congrFun h1 i) i
  simp only [Matrix.mul_apply, conjT, Matrix.transpose_apply, Matrix.map_apply, Matrix.one_apply_eq] at h2
  have h3 := congrArg τ h2
  simp only [map_sum, map_mul, map_one] at h3
  have h4 : ∑ k, (‖τ ((g : Matrix (Fin n) (Fin n) L) i k)‖ ^ 2 : ℝ) = 1 := by
    have : ∑ k, ((‖τ ((g : Matrix (Fin n) (Fin n) L) i k)‖ ^ 2 : ℝ) : ℂ) = 1 := by
      rw [← h3]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [RingHom.coe_coe, IsCMField.complexEmbedding_complexConj, Complex.mul_conj']
      push_cast; rfl
    exact_mod_cast this
  have h5 : ‖τ ((g : Matrix (Fin n) (Fin n) L) i j)‖ ^ 2 ≤ 1 :=
    h4 ▸ Finset.single_le_sum (f := fun k => ‖τ ((g : Matrix (Fin n) (Fin n) L) i k)‖ ^ 2)
      (fun k _ => sq_nonneg _) (Finset.mem_univ j)
  nlinarith [norm_nonneg (τ ((g : Matrix (Fin n) (Fin n) L) i j))]

end GlobalTheory.InvFormBdd

open GlobalTheory.InvFormBdd in

theorem GlobalTheory.InvFormBdd.exists_isInvForm : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n),
    ∃ β, IsInvForm a β := by
  intro L _ _ _ n a
  classical
  obtain ⟨_, ι, _, _, b, P, hP⟩ := a.alg
  let f : GQ L n →* Matrix.GeneralLinearGroup ι ℂ :=
    (Units.map (LinearMap.toMatrixAlgEquiv b).toMonoidHom).comp a.ρ.asGroupHom
  have hf : ∀ γ, ((f γ : Matrix.GeneralLinearGroup ι ℂ) : Matrix ι ι ℂ) = LinearMap.toMatrix b b (a.ρ γ) := by
    intro γ; ext i j; simp [f, LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply, Representation.asGroupHom_apply]
  let C : ℝ := ∑ i, ∑ j, ∑ d ∈ (P i j).support, ‖MvPolynomial.coeff d (P i j)‖
  have hC : ∀ h ∈ f.range, ∀ i j, ‖(h : Matrix ι ι ℂ) i j‖ ≤ C := by
    rintro _ ⟨γ, rfl⟩ i j
    have hγ := γ.2
    unfold GQ at hγ
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map] at hγ
    obtain ⟨g, hg, e⟩ := hγ
    have e' : (((γ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
        (g : Matrix (Fin n) (Fin n) L).map (Algebra.TensorProduct.includeLeftRingHom) := by
      rw [← e]; rfl
    rw [hf, hP γ g e']
    refine (norm_eval_le _ _ fun p => norm_emb_le_one g hg _ _ _).trans ?_
    refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j, ∑ d ∈ (P i j).support, ‖MvPolynomial.coeff d (P i j)‖)
      (fun i _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i))
    exact Finset.single_le_sum (f := fun j => ∑ d ∈ (P i j).support, ‖MvPolynomial.coeff d (P i j)‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ j)
  obtain ⟨β₀, h1, h2, h3⟩ := exists_form_of_bounded f.range C hC
  let e : a.W →ₗ[ℂ] (ι → ℂ) := b.equivFun.toLinearMap
  refine ⟨(β₀.comp e).compl₂ e, fun x y => ?_, fun x hx => ?_, fun γ x y => ?_⟩
  · exact h1 _ _
  · refine h2 _ ?_
    simpa [e] using hx
  · show β₀ (e (a.ρ γ x)) (e (a.ρ γ y)) = β₀ (e x) (e y)
    have hv : ∀ z, e (a.ρ γ z) = ((f γ : Matrix.GeneralLinearGroup ι ℂ) : Matrix ι ι ℂ) *ᵥ e z := by
      intro z
      rw [hf]
      exact (LinearMap.toMatrix_mulVec_repr b b (a.ρ γ) z).symm
    rw [hv, hv]
    exact h3 _ ⟨γ, rfl⟩ _ _
