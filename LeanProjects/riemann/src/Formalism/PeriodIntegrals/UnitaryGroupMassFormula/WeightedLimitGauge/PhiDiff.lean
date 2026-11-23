import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushLoc

noncomputable section

open Matrix NormedSpace

namespace PI.RhsWLim.W

open PI.RhsWLim

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {k r : ℕ}

lemma opBeta_add (q q' : TrE k) (a : Fin k) :
    opBeta k (q + q') a = opBeta k q a + opBeta k q' a := by
  simp only [opBeta, PiLp.add_apply, Complex.ofReal_add]; ring

lemma opBeta_smul (c : ℝ) (q : TrE k) (a : Fin k) :
    opBeta k (c • q) a = (c : ℂ) * opBeta k q a := by
  simp only [opBeta, PiLp.smul_apply, smul_eq_mul, Complex.ofReal_mul]; ring

def opGenLin (k r : ℕ) : TrE k →ₗ[ℝ] Mat k r where
  toFun := opGen k r
  map_add' q q' := by
    ext i j
    simp only [opGen, Matrix.add_apply]
    split_ifs <;> simp [opBeta_add, star_add]; ring
  map_smul' c q := by
    ext i j
    simp only [opGen, Matrix.smul_apply, RingHom.id_apply]
    split_ifs <;> simp [opBeta_smul, Complex.real_smul, star_mul', Complex.conj_ofReal]; ring

def opGenL (k r : ℕ) : TrE k →L[ℝ] Mat k r := LinearMap.toContinuousLinearMap (opGenLin k r)

@[simp] lemma opGenL_apply (q : TrE k) : opGenL k r q = opGen k r q := rfl

lemma opGen_zero : opGen k r (0 : TrE k) = 0 := (opGenLin k r).map_zero

def mvL (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) : Mat k r →L[ℝ] (Fin (2 * r + k + 1) → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M *ᵥ v
      map_add' := fun M N => Matrix.add_mulVec M N v
      map_smul' := fun c M => by simp [Matrix.smul_mulVec] }

@[simp] lemma mvL_apply (v : Fin (2 * r + k + 1) → ℂ) (M : Mat k r) : mvL k r v M = M *ᵥ v := rfl

def psiV (k r : ℕ) (T' : ℝ) (q : TrE k) : Fin (2 * r + k + 1) → ℂ :=
  NormedSpace.exp (opGen k r q) *ᵥ opBase k r T'

lemma psiV_zero (T' : ℝ) : psiV k r T' 0 = opBase k r T' := by
  simp [psiV, opGen_zero, NormedSpace.exp_zero]

lemma opBase_last (T' : ℝ) : opBase k r T' (wI k r (Fin.last k)) = (Real.sqrt T' : ℂ) := by
  simp [opBase, wLast, bvec]

lemma mulVec_base (T' : ℝ) (M : Mat k r) (i : Fin (2 * r + k + 1)) :
    (M *ᵥ opBase k r T') i = (Real.sqrt T' : ℂ) * M i (wI k r (Fin.last k)) := by
  simp [opBase, wLast, bvec, Matrix.mulVec_smul]

lemma opGen_y (q : TrE k) (a : Fin k) :
    opGen k r q (wI k r a.castSucc) (wI k r (Fin.last k)) = opBeta k q a := by
  simp [opGen, wI, a.isLt]

lemma opGen_c (q : TrE k) :
    opGen k r q (wI k r (Fin.last k)) (wI k r (Fin.last k)) = (q none : ℂ) * Complex.I := by
  simp [opGen, wI]

lemma psiV_contDiffAt (T' : ℝ) : ContDiffAt ℝ 1 (psiV k r T') 0 := by
  have h1 : ContDiffAt ℝ 1 (opGen k r) (0 : TrE k) := (opGenL k r).contDiff.contDiffAt
  have h2 : ContDiffAt ℝ 1 (NormedSpace.exp : Mat k r → Mat k r) (opGen k r 0) :=
    (exp_analytic (𝕂 := ℝ) (opGen k r 0)).contDiffAt
  exact (mvL k r (opBase k r T')).contDiff.contDiffAt.comp (0 : TrE k) (h2.comp (0 : TrE k) h1)

lemma psiV_strict (T' : ℝ) : HasStrictFDerivAt (psiV k r T')
    ((mvL k r (opBase k r T')).comp ((1 : Mat k r →L[ℝ] Mat k r).comp (opGenL k r))) 0 := by
  have h1 : HasStrictFDerivAt (opGen k r) (opGenL k r) (0 : TrE k) := (opGenL k r).hasStrictFDerivAt
  have h2 : HasStrictFDerivAt (NormedSpace.exp : Mat k r → Mat k r) (1 : Mat k r →L[ℝ] Mat k r)
      (opGen k r 0) := by
    rw [opGen_zero]
    exact hasStrictFDerivAt_exp_zero_of_radius_pos (expSeries_radius_pos ℝ (Mat k r))
  exact (mvL k r (opBase k r T')).hasStrictFDerivAt.comp (0 : TrE k) (h2.comp (0 : TrE k) h1)

lemma dpsi_apply (T' : ℝ) (q : TrE k) (i : Fin (2 * r + k + 1)) :
    ((mvL k r (opBase k r T')).comp ((1 : Mat k r →L[ℝ] Mat k r).comp (opGenL k r))) q i
      = (Real.sqrt T' : ℂ) * opGen k r q i (wI k r (Fin.last k)) := by
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply, opGenL_apply, mvL_apply]
  exact mulVec_base T' _ i

def dgn (T' : ℝ) : Option (Fin k × Bool) → ℝ := fun o => match o with
  | none => 1
  | some _ => Real.sqrt T' / Real.sqrt 2

def DL (k : ℕ) (T' : ℝ) : TrE k →L[ℝ] TrE k := LinearMap.toContinuousLinearMap
  { toFun := fun q => (WithLp.equiv 2 (Option (Fin k × Bool) → ℝ)).symm (fun o => dgn T' o * q o)
    map_add' := fun q q' => by ext o; simp [mul_add]
    map_smul' := fun c q => by ext o; simp; ring }

@[simp] lemma DL_apply (T' : ℝ) (q : TrE k) (o : Option (Fin k × Bool)) : DL k T' q o = dgn T' o * q o := rfl

lemma DL_det (T' : ℝ) (hT : 0 < T') : (DL k T').det = (T' / 2) ^ k := by
  show LinearMap.det (DL k T' : TrE k →ₗ[ℝ] TrE k) = _
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Option (Fin k × Bool)) ℝ).toBasis]
  have hm : LinearMap.toMatrix (EuclideanSpace.basisFun (Option (Fin k × Bool)) ℝ).toBasis
      (EuclideanSpace.basisFun (Option (Fin k × Bool)) ℝ).toBasis (DL k T' : TrE k →ₗ[ℝ] TrE k)
      = Matrix.diagonal (dgn T') := by
    ext i j
    rw [LinearMap.toMatrix_apply, Matrix.diagonal_apply]
    simp only [OrthonormalBasis.coe_toBasis, OrthonormalBasis.coe_toBasis_repr_apply,
      EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply, ContinuousLinearMap.coe_coe, DL_apply]
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  rw [hm, Matrix.det_diagonal, Fintype.prod_option]
  simp only [dgn, one_mul]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool,
    mul_comm k 2, pow_mul, div_pow, Real.sq_sqrt hT.le, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]

lemma phiT_coord_c (T' : ℝ) (q : TrE k) :
    phiT k r T' q none = (Complex.log (psiV k r T' q (wI k r (Fin.last k)))).im := by
  rw [Complex.log_im]; rfl

lemma psiV_last_zero (T' : ℝ) : psiV k r T' 0 (wI k r (Fin.last k)) = (Real.sqrt T' : ℂ) := by
  rw [psiV_zero, opBase_last]

lemma beta_re_im (T' : ℝ) (q : TrE k) (a : Fin k) :
    (Real.sqrt T' : ℂ) * opBeta k q a =
      ((Real.sqrt T' / Real.sqrt 2 * q (some (a, false)) : ℝ) : ℂ)
        + ((Real.sqrt T' / Real.sqrt 2 * q (some (a, true)) : ℝ) : ℂ) * Complex.I := by
  have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; positivity
  simp only [opBeta]
  push_cast
  field_simp

theorem phiT_contDiffAt (T' : ℝ) (hT : 0 < T') : ContDiffAt ℝ 1 (phiT k r T') 0 := by
  have hp := psiV_contDiffAt (k := k) (r := r) T'
  refine (contDiffAt_piLp 2).2 fun o => ?_
  rcases o with _ | ⟨a, b⟩
  · have hlog : ContDiffAt ℝ 1 Complex.log (psiV k r T' 0 (wI k r (Fin.last k))) := by
      rw [psiV_last_zero]
      exact (Complex.contDiffAt_log (Complex.ofReal_mem_slitPlane.2 (Real.sqrt_pos.2 hT))).restrict_scalars ℝ
    have := Complex.imCLM.contDiff.contDiffAt.comp (0 : TrE k)
      (hlog.comp (0 : TrE k) ((ContinuousLinearMap.proj (R := ℝ) (wI k r (Fin.last k))).contDiff.contDiffAt.comp
        (0 : TrE k) hp))
    refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun q => ?_)
    exact phiT_coord_c T' q
  · have hj := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (2 * r + k + 1) => ℂ)
      (wI k r a.castSucc)).contDiff.contDiffAt.comp (0 : TrE k) hp
    cases b
    · exact Complex.reCLM.contDiff.contDiffAt.comp (0 : TrE k) hj
    · exact Complex.imCLM.contDiff.contDiffAt.comp (0 : TrE k) hj

theorem phiT_strict (T' : ℝ) (hT : 0 < T') : HasStrictFDerivAt (phiT k r T') (DL k T') 0 := by
  have hp := psiV_strict (k := k) (r := r) T'
  refine (hasStrictFDerivAt_piLp 2).2 fun o => ?_
  rcases o with _ | ⟨a, b⟩
  · have hs : ((Real.sqrt T' : ℝ) : ℂ) ∈ Complex.slitPlane :=
      Complex.ofReal_mem_slitPlane.2 (Real.sqrt_pos.2 hT)
    have hlog := ((Complex.hasStrictDerivAt_log hs).hasStrictFDerivAt).restrictScalars ℝ
    rw [← psiV_last_zero (k := k) (r := r)] at hlog
    have H := Complex.imCLM.hasStrictFDerivAt.comp (0 : TrE k)
      (hlog.comp (0 : TrE k) ((ContinuousLinearMap.proj (R := ℝ) (wI k r (Fin.last k))).hasStrictFDerivAt.comp
        (0 : TrE k) hp))
    have hf : (fun x => phiT k r T' x none) =
        Complex.imCLM ∘ Complex.log ∘ (fun f : Fin (2 * r + k + 1) → ℂ => f (wI k r (Fin.last k))) ∘ psiV k r T' := by
      funext x; exact phiT_coord_c T' x
    rw [hf]
    refine H.congr_fderiv (ContinuousLinearMap.ext fun q => ?_)
    have hsq : (Real.sqrt T' : ℂ) ≠ 0 := by rw [Complex.ofReal_ne_zero]; positivity
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, ContinuousLinearMap.proj_apply,
      opGenL_apply, mvL_apply, mulVec_base, opGen_c, psiV_last_zero, Complex.imCLM_apply, PiLp.proj_apply,
      DL_apply, dgn, one_mul, smul_eq_mul]
    have : (Real.sqrt T' : ℂ) * ((q none : ℂ) * Complex.I) * (Real.sqrt T' : ℂ)⁻¹ = (q none : ℂ) * Complex.I := by
      field_simp
    rw [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, this]; simp
  · have Hj := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (2 * r + k + 1) => ℂ)
      (wI k r a.castSucc)).hasStrictFDerivAt.comp (0 : TrE k) hp
    cases b
    · have H := Complex.reCLM.hasStrictFDerivAt.comp (0 : TrE k) Hj
      refine H.congr_fderiv (ContinuousLinearMap.ext fun q => ?_)
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, dpsi_apply, opGen_y,
        beta_re_im, Complex.reCLM_apply, PiLp.proj_apply, DL_apply, dgn]
      change ((opGen k r q *ᵥ opBase k r T') (wI k r a.castSucc)).re = _
      rw [mulVec_base, opGen_y, beta_re_im]
      simp
    · have H := Complex.imCLM.hasStrictFDerivAt.comp (0 : TrE k) Hj
      refine H.congr_fderiv (ContinuousLinearMap.ext fun q => ?_)
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, dpsi_apply, opGen_y,
        beta_re_im, Complex.imCLM_apply, PiLp.proj_apply, DL_apply, dgn]
      change ((opGen k r q *ᵥ opBase k r T') (wI k r a.castSucc)).im = _
      rw [mulVec_base, opGen_y, beta_re_im]
      simp

theorem hermitianDefectAdd : PhiDiff := by
  intro k r T' _ hT
  refine ⟨phiT_contDiffAt T' hT, ?_⟩
  rw [(phiT_strict (r := r) T' hT).hasFDerivAt.fderiv]
  exact DL_det T' hT

end PI.RhsWLim.W
