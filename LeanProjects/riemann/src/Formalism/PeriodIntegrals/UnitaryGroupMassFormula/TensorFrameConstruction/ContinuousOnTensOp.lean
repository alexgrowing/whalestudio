import Mathlib

noncomputable section

open scoped InnerProductSpace ComplexConjugate
open Module

namespace PI.ScPiBuildW.Tens

variable {ι : Type} [Fintype ι] [DecidableEq ι]

abbrev Idx (Vl : ι → Type) [∀ i, NormedAddCommGroup (Vl i)] [∀ i, InnerProductSpace ℂ (Vl i)] : Type :=
  ∀ i, Fin (finrank ℂ (Vl i))

abbrev TV (Vl : ι → Type) [∀ i, NormedAddCommGroup (Vl i)] [∀ i, InnerProductSpace ℂ (Vl i)] : Type :=
  EuclideanSpace ℂ (Idx Vl)

variable {Vl : ι → Type} [∀ i, NormedAddCommGroup (Vl i)] [∀ i, InnerProductSpace ℂ (Vl i)]
  [∀ i, FiniteDimensional ℂ (Vl i)]

def bas (Vl : ι → Type) [∀ i, NormedAddCommGroup (Vl i)] [∀ i, InnerProductSpace ℂ (Vl i)]
    [∀ i, FiniteDimensional ℂ (Vl i)] (i : ι) : OrthonormalBasis (Fin (finrank ℂ (Vl i))) ℂ (Vl i) :=
  stdOrthonormalBasis ℂ (Vl i)

def tensU (x : ∀ i, Vl i) : TV Vl :=
  WithLp.toLp 2 (fun p : Idx Vl => ∏ i, ⟪bas Vl i (p i), x i⟫_ℂ)

theorem tensU_apply (x : ∀ i, Vl i) (p : Idx Vl) : tensU x p = ∏ i, ⟪bas Vl i (p i), x i⟫_ℂ := rfl

theorem prod_sum_pi {κ : ι → Type} [∀ i, Fintype (κ i)] (f : ∀ i, κ i → ℂ) :
    ∏ i, ∑ j, f i j = ∑ p : (∀ i, κ i), ∏ i, f i (p i) := by
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

theorem inner_tensU (x y : ∀ i, Vl i) : ⟪tensU x, tensU y⟫_ℂ = ∏ i, ⟪x i, y i⟫_ℂ := by
  rw [PiLp.inner_apply]
  simp only [tensU_apply, RCLike.inner_apply, map_prod]
  have h : ∀ i, ⟪x i, y i⟫_ℂ = ∑ j, (starRingEnd ℂ) ⟪bas Vl i j, x i⟫_ℂ * ⟪bas Vl i j, y i⟫_ℂ := by
    intro i
    rw [← (bas Vl i).sum_inner_mul_inner (x i) (y i)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_conj_symm]
  simp_rw [h, prod_sum_pi, ← Finset.prod_mul_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  refine Finset.prod_congr rfl fun i _ => ?_
  ring

theorem tensU_basis (p : Idx Vl) : tensU (fun i => bas Vl i (p i)) = EuclideanSpace.single p 1 := by
  ext q
  rw [tensU_apply, PiLp.single_apply]
  by_cases hqp : q = p
  · subst hqp
    simp only [if_true]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [inner_self_eq_norm_sq_to_K, (bas Vl i).orthonormal.1 (q i)]
    simp
  · rw [if_neg hqp]
    obtain ⟨i, hi⟩ : ∃ i, q i ≠ p i := by
      by_contra hne
      push Not at hne
      exact hqp (funext hne)
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    exact (bas Vl i).orthonormal.2 hi

theorem span_tensU : Submodule.span ℂ (Set.range (tensU (Vl := Vl))) = ⊤ := by
  refine eq_top_iff.2 ?_
  rw [← (EuclideanSpace.basisFun (Idx Vl) ℂ).toBasis.span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨p, rfl⟩
  refine ⟨fun i => bas Vl i (p i), ?_⟩
  rw [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply, tensU_basis]

theorem eq_of_inner_tensU {v v' : TV Vl} (h : ∀ x, ⟪tensU x, v⟫_ℂ = ⟪tensU x, v'⟫_ℂ) : v = v' := by
  have hd : ∀ x, ⟪v - v', tensU x⟫_ℂ = 0 := fun x => by
    rw [← inner_conj_symm, inner_sub_right, h x, sub_self, map_zero]
  have h0 : (innerSL ℂ (v - v')).toLinearMap = 0 :=
    LinearMap.ext_on_range span_tensU (fun x => by simpa using hd x)
  have h2 : ⟪v - v', v - v'⟫_ℂ = 0 := by
    have := LinearMap.congr_fun h0 (v - v')
    simp only [ContinuousLinearMap.coe_coe, innerSL_apply_apply, LinearMap.zero_apply] at this
    exact this
  exact sub_eq_zero.1 (inner_self_eq_zero.1 h2)

theorem clm_ext {T T' : TV Vl →L[ℂ] TV Vl} (h : ∀ x, T (tensU x) = T' (tensU x)) : T = T' :=
  ContinuousLinearMap.coe_inj.1 (LinearMap.ext_on_range span_tensU h)

def opMat (A : ∀ i, Vl i →L[ℂ] Vl i) : Matrix (Idx Vl) (Idx Vl) ℂ :=
  fun p q => ∏ i, ⟪bas Vl i (p i), A i (bas Vl i (q i))⟫_ℂ

def tensOp (A : ∀ i, Vl i →L[ℂ] Vl i) : TV Vl →L[ℂ] TV Vl :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (opMat A))

theorem tensOp_apply (A : ∀ i, Vl i →L[ℂ] Vl i) (v : TV Vl) (p : Idx Vl) :
    tensOp A v p = ∑ q, opMat A p q * v q := by
  simp only [tensOp, LinearMap.coe_toContinuousLinearMap']
  rw [Matrix.piLp_ofLp_toEuclideanLin, Matrix.toLin'_apply, Matrix.mulVec, dotProduct]

theorem sum_inner_op {V' : Type} [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] (A : V' →L[ℂ] V')
    {m : Type} [Fintype m] (b : OrthonormalBasis m ℂ V') (u x : V') :
    ∑ j, ⟪u, A (b j)⟫_ℂ * ⟪b j, x⟫_ℂ = ⟪u, A x⟫_ℂ := by
  conv_rhs => rw [← b.sum_repr' x]
  rw [map_sum, inner_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, inner_smul_right, mul_comm]

theorem tensOp_tensU (A : ∀ i, Vl i →L[ℂ] Vl i) (x : ∀ i, Vl i) :
    tensOp A (tensU x) = tensU (fun i => A i (x i)) := by
  ext p
  rw [tensOp_apply, tensU_apply]
  simp only [opMat, tensU_apply, ← Finset.prod_mul_distrib]
  rw [← prod_sum_pi (fun i j => ⟪bas Vl i (p i), A i (bas Vl i j)⟫_ℂ * ⟪bas Vl i j, x i⟫_ℂ)]
  refine Finset.prod_congr rfl fun i _ => ?_
  exact sum_inner_op (A i) (bas Vl i) _ _

theorem tensOp_one : tensOp (fun i => (1 : Vl i →L[ℂ] Vl i)) = 1 :=
  clm_ext fun x => by rw [tensOp_tensU]; rfl

theorem tensOp_mul (A B : ∀ i, Vl i →L[ℂ] Vl i) :
    tensOp (fun i => A i * B i) = tensOp A * tensOp B :=
  clm_ext fun x => by
    rw [ContinuousLinearMap.mul_apply, tensOp_tensU, tensOp_tensU, tensOp_tensU]
    rfl

theorem inner_tensOp (A : ∀ i, Vl i →L[ℂ] Vl i) (hA : ∀ i (u w : Vl i), ⟪A i u, A i w⟫_ℂ = ⟪u, w⟫_ℂ)
    (u w : TV Vl) : ⟪tensOp A u, tensOp A w⟫_ℂ = ⟪u, w⟫_ℂ := by
  have hQ : (ContinuousLinearMap.adjoint (tensOp A)) * tensOp A = 1 := clm_ext fun y => by
    refine eq_of_inner_tensU fun x => ?_
    rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.adjoint_inner_right, tensOp_tensU,
      tensOp_tensU, ContinuousLinearMap.one_apply, inner_tensU, inner_tensU]
    exact Finset.prod_congr rfl fun i _ => hA i (x i) (y i)
  rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.mul_apply, hQ,
    ContinuousLinearMap.one_apply]

theorem continuousOn_tensOp {X : Type*} [TopologicalSpace X] (A : X → ∀ i, Vl i →L[ℂ] Vl i) (S : Set X)
    (hA : ∀ i (y : Vl i), ContinuousOn (fun s => A s i y) S) (v : TV Vl) :
    ContinuousOn (fun s => tensOp (A s) v) S := by
  have hrep : (fun s => tensOp (A s) v) =
      fun s => ∑ p, (tensOp (A s) v p) • EuclideanSpace.basisFun (Idx Vl) ℂ p := by
    funext s
    conv_lhs => rw [← (EuclideanSpace.basisFun (Idx Vl) ℂ).sum_repr' (tensOp (A s) v)]
    simp only [EuclideanSpace.basisFun_inner]
  rw [hrep]
  refine continuousOn_finsetSum _ fun p _ =>
    (show ContinuousOn (fun s => tensOp (A s) v p) S from ?_).smul continuousOn_const
  simp only [tensOp_apply]
  refine continuousOn_finsetSum _ fun q _ =>
    (show ContinuousOn (fun s => opMat (A s) p q) S from ?_).mul continuousOn_const
  simp only [opMat]
  refine continuousOn_finsetProd _ fun i _ => ?_
  exact ContinuousOn.inner continuousOn_const (hA i _)

end PI.ScPiBuildW.Tens
