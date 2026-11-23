import Mathlib
import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles

namespace GroundTheory.Global

open IsDedekindDomain NumberField Topology AdeleBaseChange
open scoped NumberField.AdeleRing

noncomputable section

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

namespace AdeleBaseChange

variable (K L) in

def adeleRingAut : (L ≃ₐ[K] L) →* RingAut 𝔸[L] where
  toFun σ := adeleRingEquiv (σ : L ≃+* L)
  map_one' := adeleRingEquiv_refl
  map_mul' σ τ := by
    rw [show ((σ * τ : L ≃ₐ[K] L) : L ≃+* L) = (τ : L ≃+* L).trans (σ : L ≃+* L) from rfl,
      adeleRingEquiv_trans]
    rfl

instance : MulSemiringAction (L ≃ₐ[K] L) 𝔸[L] :=
  MulSemiringAction.compHom _ (adeleRingAut K L)

omit [NumberField K] in

@[simp]
theorem smul_algebraMap (σ : L ≃ₐ[K] L) (l : L) :
    σ • algebraMap L 𝔸[L] l = algebraMap L 𝔸[L] (σ l) :=
  adeleRingEquiv_algebraMap _ l

@[simp]
theorem smul_adeleMap (σ : L ≃ₐ[K] L) (a : 𝔸[K]) : σ • adeleMap K L a = adeleMap K L a :=
  adeleRingEquiv_adeleMap σ a

instance : ContinuousConstSMul (L ≃ₐ[K] L) 𝔸[L] where
  continuous_const_smul σ := continuous_adeleRingEquiv (σ : L ≃+* L)

instance : ContinuousSMul (L ≃ₐ[K] L) 𝔸[L] where
  continuous_smul := continuous_prod_of_discrete_left.2 fun σ ↦ continuous_const_smul σ

@[simp]
theorem norm_smul (σ : L ≃ₐ[K] L) (y : 𝔸[L]) : Algebra.norm 𝔸[K] (σ • y) = Algebra.norm 𝔸[K] y :=
  norm_adeleRingEquiv σ y

section Galois

variable [IsGalois K L]

open Classical in

theorem isUnit_det_conjugates (b : Module.Basis (L ≃ₐ[K] L) K L) :
    IsUnit (Matrix.of fun σ τ : L ≃ₐ[K] L ↦ σ (b τ)).det := by
  classical
  set D := Matrix.of fun σ τ : L ≃ₐ[K] L ↦ σ (b τ)
  have hT : D.transpose * D = (Algebra.traceMatrix K b).map (algebraMap K L) := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply,
      Algebra.traceMatrix_apply, Algebra.traceForm_apply, D]
    rw [trace_eq_sum_automorphisms]
    exact Finset.sum_congr rfl fun σ _ ↦ (map_mul σ _ _).symm
  have hdet : D.det * D.det = algebraMap K L (Algebra.discr K b) := by
    rw [Algebra.discr_def, RingHom.map_det, RingHom.mapMatrix_apply, ← hT, Matrix.det_mul,
      Matrix.det_transpose]
  refine isUnit_iff_ne_zero.2 fun h ↦ Algebra.discr_not_zero_of_basis K b ?_
  rw [h, zero_mul] at hdet
  exact (FaithfulSMul.algebraMap_injective K L) (hdet.symm.trans (map_zero _).symm)

theorem adeleMap_norm (y : 𝔸[L]) :
    adeleMap K L (Algebra.norm 𝔸[K] y) = ∏ σ : L ≃ₐ[K] L, σ • y := by
  classical
  have hcard : Fintype.card (L ≃ₐ[K] L) = Module.finrank K L := by
    rw [Fintype.card_eq_nat_card]; exact IsGalois.card_aut_eq_finrank K L
  let b : Module.Basis (L ≃ₐ[K] L) K L :=
    (Module.finBasis K L).reindex (Fintype.equivFinOfCardEq hcard).symm
  let B := adeleBasis b
  let M := Algebra.leftMulMatrix B y
  let D : Matrix (L ≃ₐ[K] L) (L ≃ₐ[K] L) L := Matrix.of fun σ τ ↦ σ (b τ)
  have hM : ∀ ρ τ, M ρ τ = B.repr (y * B τ) ρ := fun ρ τ ↦
    Algebra.leftMulMatrix_eq_repr_mul B y ρ τ
  have hy : ∀ τ, y * algebraMap L 𝔸[L] (b τ) =
      ∑ ρ, adeleMap K L (M ρ τ) * algebraMap L 𝔸[L] (b ρ) := by
    intro τ
    conv_lhs => rw [← B.sum_repr (y * algebraMap L 𝔸[L] (b τ))]
    refine Finset.sum_congr rfl fun ρ _ ↦ ?_
    rw [Algebra.smul_def, algebraMap_adeleRing, adeleBasis_apply, hM, adeleBasis_apply]
  have key : Matrix.diagonal (fun σ : L ≃ₐ[K] L ↦ σ • y) * D.map (algebraMap L 𝔸[L]) =
      D.map (algebraMap L 𝔸[L]) * M.map (adeleMap K L) := by
    ext σ τ
    rw [Matrix.diagonal_mul, Matrix.mul_apply]
    have h := congrArg (σ • ·) (hy τ)
    simp only [smul_mul', Finset.smul_sum, smul_algebraMap, smul_adeleMap] at h
    simp only [Matrix.map_apply, Matrix.of_apply, D, h]
    exact Finset.sum_congr rfl fun ρ _ ↦ mul_comm _ _
  have hdet := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, ← RingHom.mapMatrix_apply,
    ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← RingHom.map_det] at hdet
  rw [Algebra.norm_eq_matrix_det B]
  rw [mul_comm] at hdet
  exact (((isUnit_det_conjugates b).map (algebraMap L 𝔸[L])).mul_left_cancel hdet).symm

theorem exists_adeleMap_eq_sum_smul (y : 𝔸[L]) :
    ∃ a : 𝔸[K], adeleMap K L a = ∑ σ : L ≃ₐ[K] L, σ • y := by
  classical
  let b := Module.finBasis K L
  let B := adeleBasis b
  refine ⟨∑ i, B.repr y i * algebraMap K 𝔸[K] (Algebra.trace K L (b i)), ?_⟩
  have hy : y = ∑ i, adeleMap K L (B.repr y i) * algebraMap L 𝔸[L] (b i) := by
    conv_lhs => rw [← B.sum_repr y]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Algebra.smul_def, algebraMap_adeleRing, adeleBasis_apply]
  conv_rhs => rw [hy]
  simp only [Finset.smul_sum, smul_mul', smul_adeleMap, smul_algebraMap]
  rw [Finset.sum_comm, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← Finset.mul_sum, ← map_sum, ← trace_eq_sum_automorphisms, map_mul,
    adeleMap_algebraMap]

theorem forall_smul_eq_iff_mem_range (y : 𝔸[L]) :
    (∀ σ : L ≃ₐ[K] L, σ • y = y) ↔ y ∈ (adeleMap K L).range := by
  constructor
  · intro hy
    obtain ⟨a, ha⟩ := exists_adeleMap_eq_sum_smul (K := K) y
    simp only [hy, Finset.sum_const, Finset.card_univ] at ha
    set n := Fintype.card (L ≃ₐ[K] L)
    have hn : (n : K) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    refine ⟨algebraMap K 𝔸[K] (n : K)⁻¹ * a, ?_⟩
    rw [map_mul, ha, adeleMap_algebraMap, nsmul_eq_mul, ← mul_assoc,
      show (n : 𝔸[L]) = algebraMap L 𝔸[L] (algebraMap K L (n : K)) by simp, ← map_mul, ← map_mul,
      inv_mul_cancel₀ hn, map_one, map_one, one_mul]
  · rintro ⟨a, rfl⟩ σ
    exact smul_adeleMap σ a

end Galois

end AdeleBaseChange

instance : MulDistribMulAction (L ≃ₐ[K] L) (IdeleGroup L) :=
  Units.mulDistribMulActionRight

omit [NumberField K] in
@[simp]
theorem coe_smul_idele (σ : L ≃ₐ[K] L) (x : IdeleGroup L) :
    ((σ • x : IdeleGroup L) : 𝔸[L]) = σ • (x : 𝔸[L]) :=
  rfl

omit [NumberField K] in

theorem smul_idele_eq_ideleEquiv (σ : L ≃ₐ[K] L) (x : IdeleGroup L) :
    σ • x = ideleEquiv (σ : L ≃+* L) x :=
  Units.ext rfl

instance : ContinuousConstSMul (L ≃ₐ[K] L) (IdeleGroup L) where
  continuous_const_smul σ := by
    have h : (fun x : IdeleGroup L ↦ σ • x) = ideleEquiv (σ : L ≃+* L) :=
      funext (smul_idele_eq_ideleEquiv σ)
    rw [h]
    exact (ideleEquiv (σ : L ≃+* L)).continuous

instance : ContinuousSMul (L ≃ₐ[K] L) (IdeleGroup L) where
  continuous_smul := continuous_prod_of_discrete_left.2 fun σ ↦ continuous_const_smul σ

omit [NumberField K] in

@[simp]
theorem smul_diagonal (σ : L ≃ₐ[K] L) (l : Lˣ) :
    σ • IdeleGroup.diagonal L l = IdeleGroup.diagonal L (σ • l) :=
  Units.ext (smul_algebraMap σ (l : L))

@[simp]
theorem smul_ideleEmbedding (σ : L ≃ₐ[K] L) (x : IdeleGroup K) :
    σ • ideleEmbedding K L x = ideleEmbedding K L x :=
  Units.ext (smul_adeleMap σ (x : 𝔸[K]))

@[simp]
theorem ideleNorm_smul (σ : L ≃ₐ[K] L) (x : IdeleGroup L) :
    ideleNorm K L (σ • x) = ideleNorm K L x :=
  Units.ext (norm_smul σ (x : 𝔸[L]))

section Galois

variable [IsGalois K L]

theorem ideleEmbedding_ideleNorm (x : IdeleGroup L) :
    ideleEmbedding K L (ideleNorm K L x) = ∏ σ : L ≃ₐ[K] L, σ • x :=
  Units.ext (by rw [coe_ideleEmbedding, coe_ideleNorm, adeleMap_norm, Units.coe_prod]; rfl)

theorem forall_smul_eq_iff_mem_range_ideleEmbedding (x : IdeleGroup L) :
    (∀ σ : L ≃ₐ[K] L, σ • x = x) ↔ x ∈ (ideleEmbedding K L).range := by
  constructor
  · intro hx
    obtain ⟨a, ha⟩ := (forall_smul_eq_iff_mem_range (K := K) (x : 𝔸[L])).1 fun σ ↦
      congrArg Units.val (hx σ)
    obtain ⟨a', ha'⟩ := (forall_smul_eq_iff_mem_range (K := K) ((x⁻¹ : IdeleGroup L) : 𝔸[L])).1
      fun σ ↦ congrArg Units.val (show σ • x⁻¹ = x⁻¹ by rw [smul_inv', hx σ])
    have h1 : a * a' = 1 := adeleMap_injective (K := K) (L := L) (by
      rw [map_mul, ha, ha', Units.mul_inv, map_one])
    refine ⟨⟨a, a', h1, by rw [mul_comm, h1]⟩, Units.ext ?_⟩
    exact ha
  · rintro ⟨y, rfl⟩ σ
    exact smul_ideleEmbedding σ y

theorem fixedPoints_subgroup_idele :
    FixedPoints.subgroup (L ≃ₐ[K] L) (IdeleGroup L) = (ideleEmbedding K L).range := by
  ext x
  exact forall_smul_eq_iff_mem_range_ideleEmbedding x

variable (K L) in

def ideleFixedEquiv : IdeleGroup K ≃ₜ* FixedPoints.subgroup (L ≃ₐ[K] L) (IdeleGroup L) where
  toMulEquiv := (MonoidHom.ofInjective (f := ideleEmbedding K L)
      (ideleEmbedding_injective (K := K) (L := L))).trans
    (MulEquiv.subgroupCongr fixedPoints_subgroup_idele.symm)
  continuous_toFun := continuous_ideleEmbedding.subtype_mk _
  continuous_invFun := by
    rw [(isClosedEmbedding_ideleEmbedding (K := K) (L := L)).isInducing.continuous_iff]
    convert continuous_subtype_val using 1
    funext y
    simp only [Function.comp_apply]
    exact MonoidHom.apply_ofInjective_symm _ _

end Galois

variable (K L) in

def ideleClassAut : (L ≃ₐ[K] L) →* MulAut (IdeleClassGroup L) where
  toFun σ := (ideleClassEquiv (σ : L ≃+* L)).toMulEquiv
  map_one' := MulEquiv.ext fun c ↦ ideleClassEquiv_refl c
  map_mul' σ τ := MulEquiv.ext fun c ↦ ideleClassEquiv_trans (τ : L ≃+* L) (σ : L ≃+* L) c

instance : MulDistribMulAction (L ≃ₐ[K] L) (IdeleClassGroup L) :=
  MulDistribMulAction.compHom _ (ideleClassAut K L)

omit [NumberField K] in

@[simp]
theorem smul_mk (σ : L ≃ₐ[K] L) (x : IdeleGroup L) :
    σ • IdeleClassGroup.mk L x = IdeleClassGroup.mk L (σ • x) := by
  rw [smul_idele_eq_ideleEquiv]
  rfl

instance : ContinuousConstSMul (L ≃ₐ[K] L) (IdeleClassGroup L) where
  continuous_const_smul σ := (ideleClassEquiv (σ : L ≃+* L)).continuous

instance : ContinuousSMul (L ≃ₐ[K] L) (IdeleClassGroup L) where
  continuous_smul := continuous_prod_of_discrete_left.2 fun σ ↦ continuous_const_smul σ

@[simp]
theorem smul_ideleClassMap (σ : L ≃ₐ[K] L) (c : IdeleClassGroup K) :
    σ • ideleClassMap K L c = ideleClassMap K L c := by
  obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective K c
  rw [ideleClassMap_mk, smul_mk, smul_ideleEmbedding]

@[simp]
theorem ideleClassNorm_smul (σ : L ≃ₐ[K] L) (c : IdeleClassGroup L) :
    ideleClassNorm K L (σ • c) = ideleClassNorm K L c := by
  obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective L c
  rw [smul_mk, ideleClassNorm_mk, ideleClassNorm_mk, ideleNorm_smul]

section Galois

variable [IsGalois K L]

theorem ideleClassMap_ideleClassNorm (c : IdeleClassGroup L) :
    ideleClassMap K L (ideleClassNorm K L c) = ∏ σ : L ≃ₐ[K] L, σ • c := by
  obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective L c
  simp only [ideleClassNorm_mk, ideleClassMap_mk, ideleEmbedding_ideleNorm, smul_mk, map_prod]

theorem forall_smul_eq_iff_mem_range_ideleClassMap (c : IdeleClassGroup L) :
    (∀ σ : L ≃ₐ[K] L, σ • c = c) ↔ c ∈ (ideleClassMap K L).range := by
  constructor
  · intro hc
    obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective L c
    have h1 : ∀ σ : L ≃ₐ[K] L, ∃ a : Lˣ, σ • x = x * IdeleGroup.diagonal L a := by
      intro σ
      have h := hc σ
      rw [smul_mk] at h
      obtain ⟨a, ha⟩ := QuotientGroup.eq.1 h.symm
      exact ⟨a, by rw [ha, mul_inv_cancel_left]⟩
    choose a ha using h1
    have hcoc : groupCohomology.IsMulCocycle₁ a := by
      intro σ τ
      apply IdeleGroup.diagonal_injective L
      apply mul_left_cancel (a := x)
      rw [← ha, mul_smul, ha τ, smul_mul', ha σ, smul_diagonal, map_mul, mul_assoc,
        mul_comm (IdeleGroup.diagonal L (a σ))]
    obtain ⟨β, hβ⟩ := groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units a hcoc
    have hfix : ∀ σ : L ≃ₐ[K] L, σ • (x * (IdeleGroup.diagonal L β)⁻¹) =
        x * (IdeleGroup.diagonal L β)⁻¹ := by
      intro σ
      rw [smul_mul', smul_inv', ha σ, smul_diagonal, ← hβ σ, map_div, div_eq_mul_inv, mul_assoc x,
        mul_inv_cancel_comm]
    obtain ⟨z, hz⟩ := (forall_smul_eq_iff_mem_range_ideleEmbedding _).1 hfix
    refine ⟨IdeleClassGroup.mk K z, ?_⟩
    rw [ideleClassMap_mk, hz, map_mul, map_inv, IdeleClassGroup.mk_diagonal, inv_one]
    exact mul_one (IdeleClassGroup.mk L x)
  · rintro ⟨d, rfl⟩ σ
    exact smul_ideleClassMap σ d

end Galois

end

end GroundTheory.Global
