import Mathlib

open Module Matrix
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GlobalTheory

variable {𝕜 : Type*} [RCLike 𝕜]
variable {V W X : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [NormedAddCommGroup X] [InnerProductSpace 𝕜 X]
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

variable (𝕜) in

def gramVol (v : ι → V) : ℝ := √(RCLike.re (gram 𝕜 v).det)

theorem gramVol_nonneg (v : ι → V) : 0 ≤ gramVol 𝕜 v := Real.sqrt_nonneg _

theorem gramVol_sq (v : ι → V) : ((gramVol 𝕜 v : ℝ) : 𝕜) ^ 2 = (gram 𝕜 v).det := by
  have h := (posSemidef_gram 𝕜 v).det_nonneg
  rw [RCLike.nonneg_iff] at h
  rw [← RCLike.ofReal_pow, gramVol, Real.sq_sqrt h.1]
  apply RCLike.ext <;> simp [h.2]

theorem gramVol_eq_of_sq {v : ι → V} {r : ℝ} (hr : 0 ≤ r) (h : (r : 𝕜) ^ 2 = (gram 𝕜 v).det) :
    gramVol 𝕜 v = r := by
  rw [← gramVol_sq] at h
  have : r ^ 2 = gramVol 𝕜 v ^ 2 := by exact_mod_cast h
  exact ((sq_eq_sq₀ hr (gramVol_nonneg v)).mp this).symm

theorem gramVol_of_orthonormal {v : ι → V} (hv : Orthonormal 𝕜 v) : gramVol 𝕜 v = 1 :=
  gramVol_eq_of_sq zero_le_one (by simp [gram_eq_one_iff_orthonormal.mpr hv])

theorem gramVol_of_pairwise_orthogonal {v : ι → V}
    (hv : Pairwise fun i j => ⟪v i, v j⟫_𝕜 = 0) : gramVol 𝕜 v = ∏ i, ‖v i‖ := by
  refine gramVol_eq_of_sq (Finset.prod_nonneg fun _ _ => norm_nonneg _) ?_
  have : gram 𝕜 v = diagonal fun i => ((‖v i‖ : 𝕜) ^ 2) := by
    ext i j
    by_cases h : i = j
    · subst h; simp [inner_self_eq_norm_sq_to_K]
    · simp [h, hv h]
  rw [this, det_diagonal]
  push_cast
  rw [Finset.prod_pow]

@[simp] theorem gramVol_unique [Unique ι] (v : ι → V) : gramVol 𝕜 v = ‖v default‖ := by
  rw [gramVol_of_pairwise_orthogonal (Subsingleton.pairwise), Fintype.prod_unique]

@[simp] theorem gramVol_of_isEmpty [IsEmpty ι] (v : ι → V) : gramVol 𝕜 v = 1 := by
  simp [gramVol]

omit [DecidableEq ι] [Fintype κ] [DecidableEq κ] in

theorem gram_sum_smul (v : ι → V) (Y : Matrix ι κ 𝕜) :
    gram 𝕜 (fun j => ∑ i, Y i j • v i) = Yᴴ * gram 𝕜 v * Y := by
  ext a b
  simp only [gram_apply, sum_inner, inner_sum, inner_smul_left, inner_smul_right, mul_apply,
    conjTranspose_apply, Finset.sum_mul, RCLike.star_def]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem gramVol_sum_smul (v : ι → V) (Y : Matrix ι ι 𝕜) :
    gramVol 𝕜 (fun j => ∑ i, Y i j • v i) = ‖Y.det‖ * gramVol 𝕜 v := by
  refine gramVol_eq_of_sq (mul_nonneg (norm_nonneg _) (gramVol_nonneg v)) ?_
  rw [gram_sum_smul, det_mul, det_mul, det_conjTranspose, ← gramVol_sq, RCLike.star_def]
  push_cast
  rw [mul_pow, ← RCLike.conj_mul]
  ring

theorem gramVol_eq_norm_det (b : OrthonormalBasis ι 𝕜 V) (v : ι → V) :
    gramVol 𝕜 v = ‖(b.toBasis.toMatrix v).det‖ := by
  have h := gramVol_sum_smul (b : ι → V) (b.toBasis.toMatrix v)
  rw [gramVol_of_orthonormal b.orthonormal, mul_one] at h
  rw [← h]
  congr 1
  ext j
  simpa [Basis.toMatrix_apply] using (b.sum_repr (v j)).symm

theorem norm_det_inner [FiniteDimensional 𝕜 V] (hι : Fintype.card ι = finrank 𝕜 V)
    (w v : ι → V) :
    ‖(Matrix.of fun i j => ⟪w i, v j⟫_𝕜).det‖ = gramVol 𝕜 w * gramVol 𝕜 v := by
  let b : OrthonormalBasis ι 𝕜 V :=
    (stdOrthonormalBasis 𝕜 V).reindex (Fintype.equivFinOfCardEq hι).symm
  have : (Matrix.of fun i j => ⟪w i, v j⟫_𝕜) = (b.toBasis.toMatrix w)ᴴ * b.toBasis.toMatrix v := by
    ext i j
    simp [mul_apply, Basis.toMatrix_apply, b.repr_apply_apply, b.sum_inner_mul_inner]
  rw [this, det_mul, det_conjTranspose, norm_mul, norm_star, gramVol_eq_norm_det b,
    gramVol_eq_norm_det b]

theorem gramVol_mul_gramVol_of_biorthogonal [FiniteDimensional 𝕜 V]
    (hι : Fintype.card ι = finrank 𝕜 V) {w v : ι → V}
    (h : ∀ i j, ⟪w i, v j⟫_𝕜 = if i = j then 1 else 0) : gramVol 𝕜 w * gramVol 𝕜 v = 1 := by
  rw [← norm_det_inner hι]
  have : (Matrix.of fun i j => ⟪w i, v j⟫_𝕜) = 1 := by
    ext i j; simp [h, one_apply]
  simp [this]

instance isClosed_of_hasOrthogonalProjection (U : Submodule 𝕜 V) [U.HasOrthogonalProjection] :
    IsClosed (U : Set V) := by
  rw [← U.orthogonal_orthogonal]
  exact Submodule.isClosed_orthogonal _

section NormDet

variable [FiniteDimensional 𝕜 V]

theorem normDet_eq_gramVol (T : V →ₗ[𝕜] W) (b : OrthonormalBasis ι 𝕜 V) :
    T.normDet = gramVol 𝕜 (fun i => T (b i)) :=
  (gramVol_eq_of_sq T.normDet_nonneg (by simpa using T.normDet_sq_eq_det_gram b)).symm

theorem normDet_mul_normDet_of_inner_eq [FiniteDimensional 𝕜 W] {S T : V →ₗ[𝕜] W}
    (h : finrank 𝕜 V = finrank 𝕜 W) (hST : ∀ x y, ⟪S x, T y⟫_𝕜 = ⟪x, y⟫_𝕜) :
    S.normDet * T.normDet = 1 := by
  let b := stdOrthonormalBasis 𝕜 V
  rw [normDet_eq_gramVol _ b, normDet_eq_gramVol _ b]
  refine gramVol_mul_gramVol_of_biorthogonal (by simpa using h) fun i j => ?_
  rw [hST, orthonormal_iff_ite.mp b.orthonormal]

abbrev detNorm (T : V ≃ₗ[𝕜] W) : ℝ := (T : V →ₗ[𝕜] W).normDet

@[simp] theorem detNorm_refl : detNorm (LinearEquiv.refl 𝕜 V) = 1 := LinearMap.normDet_id

@[simp] theorem detNorm_linearIsometryEquiv (f : V ≃ₗᵢ[𝕜] W) : detNorm f.toLinearEquiv = 1 :=
  f.toLinearIsometry.normDet_eq_one

variable [FiniteDimensional 𝕜 W]

def invAdjoint (T : V ≃ₗ[𝕜] W) : V ≃ₗ[𝕜] W :=
  LinearEquiv.ofLinearMap (LinearMap.adjoint (T.symm : W →ₗ[𝕜] V)) (LinearMap.adjoint (T : V →ₗ[𝕜] W))
    (by rw [← LinearMap.adjoint_comp]; simp) (by rw [← LinearMap.adjoint_comp]; simp)

theorem inner_invAdjoint_apply (T : V ≃ₗ[𝕜] W) (x y : V) :
    ⟪invAdjoint T x, T y⟫_𝕜 = ⟪x, y⟫_𝕜 := by
  change ⟪LinearMap.adjoint (T.symm : W →ₗ[𝕜] V) x, T y⟫_𝕜 = _
  rw [LinearMap.adjoint_inner_left]; simp

theorem detNorm_invAdjoint (T : V ≃ₗ[𝕜] W) : detNorm (invAdjoint T) = (detNorm T)⁻¹ :=
  eq_inv_of_mul_eq_one_left
    (normDet_mul_normDet_of_inner_eq T.finrank_eq (inner_invAdjoint_apply T))

end NormDet

section Dual

open InnerProductSpace

def dualQuotientEquivAnnihilator {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (U : Submodule 𝕜 E) : StrongDual 𝕜 (E ⧸ U) ≃ₗᵢ[𝕜] StrongDual.polarSubmodule 𝕜 U where
  toFun φ := ⟨φ ∘L U.mkQL, (StrongDual.mem_polarSubmodule 𝕜 U _).mpr fun x hx => by
    simp [(Submodule.Quotient.mk_eq_zero U).mpr hx]⟩
  invFun ψ := U.liftQL (ψ : StrongDual 𝕜 E) fun x hx =>
    (StrongDual.mem_polarSubmodule 𝕜 U _).mp ψ.2 x hx
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv φ := by
    ext q
    obtain ⟨x, rfl⟩ := U.mkQ_surjective q
    rfl
  right_inv ψ := rfl
  norm_map' φ := by
    change ‖φ ∘L U.mkQL‖ = ‖φ‖
    apply le_antisymm
    · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
      exact (φ.le_opNorm _).trans
        (mul_le_mul_of_nonneg_left (Submodule.Quotient.norm_mk_le U x) (norm_nonneg _))
    · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun q => ?_
      refine le_of_forall_pos_le_add fun ε hε => ?_
      have hN : 0 < ‖φ ∘L U.mkQL‖ + 1 := by positivity
      obtain ⟨x, rfl, hx⟩ := Submodule.Quotient.norm_mk_lt q (div_pos hε hN)
      calc ‖φ (Submodule.Quotient.mk x)‖ ≤ ‖φ ∘L U.mkQL‖ * ‖x‖ := (φ ∘L U.mkQL).le_opNorm x
        _ ≤ ‖φ ∘L U.mkQL‖ * (‖(Submodule.Quotient.mk x : E ⧸ U)‖ + ε / (‖φ ∘L U.mkQL‖ + 1)) := by
          gcongr
        _ ≤ _ := by
          rw [mul_add]
          gcongr
          rw [← mul_div_assoc, div_le_iff₀ hN]
          nlinarith

@[simp] theorem dualQuotientEquivAnnihilator_apply {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] (U : Submodule 𝕜 E) (φ : StrongDual 𝕜 (E ⧸ U)) (x : E) :
    (dualQuotientEquivAnnihilator U φ : StrongDual 𝕜 E) x = φ (Submodule.Quotient.mk x) := rfl

@[simp] theorem dualQuotientEquivAnnihilator_symm_apply {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] (U : Submodule 𝕜 E) (ψ : StrongDual.polarSubmodule 𝕜 U) (x : E) :
    (dualQuotientEquivAnnihilator U).symm ψ (Submodule.Quotient.mk x) =
      (ψ : StrongDual 𝕜 E) x := rfl

def dualQuotientAnnihilatorEquiv (U : Submodule 𝕜 V) [U.HasOrthogonalProjection] :
    (StrongDual 𝕜 V ⧸ StrongDual.polarSubmodule 𝕜 U) ≃ₗᵢ[𝕜] StrongDual 𝕜 U where
  toLinearEquiv := LinearEquiv.ofLinearMap
    ((StrongDual.polarSubmodule 𝕜 U).liftQ (U.subtypeL.precomp 𝕜).toLinearMap fun φ hφ => by
      ext x
      exact (StrongDual.mem_polarSubmodule 𝕜 U _).mp hφ x x.2)
    ((StrongDual.polarSubmodule 𝕜 U).mkQ ∘ₗ (U.orthogonalProjectionOnto.precomp 𝕜).toLinearMap)
    (by
      ext φ x
      change φ (U.orthogonalProjectionOnto (x : V)) = φ x
      simp)
    (by
      ext φ
      change Submodule.Quotient.mk _ = Submodule.Quotient.mk φ
      rw [Submodule.Quotient.eq, StrongDual.mem_polarSubmodule]
      intro x hx
      change φ (U.starProjection x) - φ x = 0
      rw [Submodule.starProjection_eq_self_iff.mpr hx, sub_self])
  norm_map' q := by
    apply le_antisymm
    · refine le_of_forall_pos_le_add fun ε hε => ?_
      obtain ⟨φ, rfl, hφ⟩ := Submodule.Quotient.norm_mk_lt q hε
      refine le_trans ?_ hφ.le
      exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => φ.le_opNorm x
    · obtain ⟨φ, rfl⟩ := (StrongDual.polarSubmodule 𝕜 U).mkQ_surjective q
      have : (StrongDual.polarSubmodule 𝕜 U).mkQ φ =
          Submodule.Quotient.mk ((φ ∘L U.subtypeL) ∘L U.orthogonalProjectionOnto) := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.eq, StrongDual.mem_polarSubmodule]
        intro x hx
        change φ x - φ (U.starProjection x) = 0
        rw [Submodule.starProjection_eq_self_iff.mpr hx, sub_self]
      conv_lhs => rw [this]
      refine (Submodule.Quotient.norm_mk_le _ _).trans ?_
      change _ ≤ ‖φ ∘L U.subtypeL‖
      refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
      exact ((φ ∘L U.subtypeL).le_opNorm _).trans
        (mul_le_mul_of_nonneg_left (U.norm_orthogonalProjectionOnto_apply_le x) (norm_nonneg _))

@[simp] theorem dualQuotientAnnihilatorEquiv_mk (U : Submodule 𝕜 V) [U.HasOrthogonalProjection]
    (φ : StrongDual 𝕜 V) (x : U) :
    dualQuotientAnnihilatorEquiv U (Submodule.Quotient.mk φ) x = φ x := rfl

variable [FiniteDimensional 𝕜 V] [FiniteDimensional 𝕜 W] [FiniteDimensional 𝕜 X]

variable (𝕜 V) in

def rieszEquiv : V ≃ₗᵢ⋆[𝕜] StrongDual 𝕜 V :=
  haveI := FiniteDimensional.complete 𝕜 V
  toDual 𝕜 V

@[simp] theorem rieszEquiv_apply (x y : V) : rieszEquiv 𝕜 V x y = ⟪x, y⟫_𝕜 := rfl

instance dualInnerProductSpace : InnerProductSpace 𝕜 (StrongDual 𝕜 V) where
  inner φ ψ := ⟪(rieszEquiv 𝕜 V).symm ψ, (rieszEquiv 𝕜 V).symm φ⟫_𝕜
  norm_sq_eq_re_inner φ := by rw [inner_self_eq_norm_sq, LinearIsometryEquiv.norm_map]
  conj_inner_symm φ ψ := inner_conj_symm _ _
  add_left φ ψ χ := by rw [map_add, inner_add_right]
  smul_left φ ψ r := by rw [map_smulₛₗ, inner_smul_right]

@[simp] theorem inner_rieszEquiv (x y : V) :
    ⟪rieszEquiv 𝕜 V x, rieszEquiv 𝕜 V y⟫_𝕜 = ⟪y, x⟫_𝕜 := by
  change ⟪(rieszEquiv 𝕜 V).symm _, (rieszEquiv 𝕜 V).symm _⟫_𝕜 = _
  simp

def strongDualMap (T : V →ₗ[𝕜] W) : StrongDual 𝕜 W →ₗ[𝕜] StrongDual 𝕜 V :=
  (T.toContinuousLinearMap.precomp 𝕜).toLinearMap

omit [FiniteDimensional 𝕜 W] in

@[simp] theorem strongDualMap_apply (T : V →ₗ[𝕜] W) (φ : StrongDual 𝕜 W) (x : V) :
    strongDualMap T φ x = φ (T x) := rfl

def strongContragredient (T : V ≃ₗ[𝕜] W) : StrongDual 𝕜 V ≃ₗ[𝕜] StrongDual 𝕜 W :=
  LinearEquiv.ofLinearMap (strongDualMap (T.symm : W →ₗ[𝕜] V)) (strongDualMap (T : V →ₗ[𝕜] W))
    (by ext φ x; simp) (by ext φ x; simp)

@[simp] theorem strongContragredient_apply (T : V ≃ₗ[𝕜] W) (φ : StrongDual 𝕜 V) (y : W) :
    strongContragredient T φ y = φ (T.symm y) := rfl

end Dual

example : gramVol ℂ (fun _ : Unit => (3 + 4 * Complex.I : ℂ)) = 5 := by
  rw [gramVol_unique, Complex.norm_eq_sqrt_sq_add_sq]
  norm_num [show (3 : ℝ) ^ 2 + 4 ^ 2 = 5 ^ 2 by norm_num]

example : gramVol ℂ (![!₂[1, 0], !₂[1, 2 * Complex.I]] : Fin 2 → EuclideanSpace ℂ (Fin 2)) = 2 := by
  rw [gramVol_eq_norm_det (EuclideanSpace.basisFun (Fin 2) ℂ), det_fin_two]
  simp [Basis.toMatrix_apply]

example [FiniteDimensional 𝕜 V] (c : 𝕜ˣ) :
    detNorm (invAdjoint (c • LinearEquiv.refl 𝕜 V)) = (‖(c : 𝕜)‖ ^ finrank 𝕜 V)⁻¹ := by
  rw [detNorm_invAdjoint]
  congr 1
  exact (LinearMap.normDet_smul (LinearMap.id : V →ₗ[𝕜] V) (c : 𝕜)).trans (by simp)

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {n : ℕ} (v : Fin n → E) : gramVol ℝ v = ‖exteriorPower.ιMulti ℝ n v‖ :=
  gramVol_eq_of_sq (norm_nonneg _)
    (by rw [← exteriorPower.inner_ιMulti_self, real_inner_self_eq_norm_sq]; simp)

example (U : Submodule ℂ (EuclideanSpace ℂ (Fin 2))) :
    InnerProductSpace ℂ (StrongDual ℂ (EuclideanSpace ℂ (Fin 2) ⧸ U)) := inferInstance

end GlobalTheory
