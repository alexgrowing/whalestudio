import Mathlib
import GroundTheory.GlobalFields.Adele.BaseChange
import GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe

namespace GroundTheory.Global

open IsDedekindDomain NumberField TensorProduct Module Topology
open scoped NumberField.AdeleRing RestrictedProduct

noncomputable section

section NormMap

variable {A B A' B' ι : Type*} [CommRing A] [CommRing B] [Algebra A B] [CommRing A']
  [CommRing B'] [Algebra A' B'] [Fintype ι] [DecidableEq ι]

theorem norm_map_of_repr (φ : A →+* A') (ψ : B →+* B') (b : Basis ι A B) (b' : Basis ι A' B')
    (h : ∀ y i, b'.repr (ψ y) i = φ (b.repr y i)) (y : B) :
    Algebra.norm A' (ψ y) = φ (Algebra.norm A y) := by
  have hb : ∀ j, ψ (b j) = b' j := fun j ↦ b'.repr.injective <| Finsupp.ext fun i ↦ by
    rw [h, b.repr_self, b'.repr_self, Finsupp.single_apply, Finsupp.single_apply]
    split_ifs <;> simp
  rw [Algebra.norm_eq_matrix_det b, Algebra.norm_eq_matrix_det b', RingHom.map_det]
  congr 1
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul, RingHom.mapMatrix_apply, Matrix.map_apply,
    Algebra.leftMulMatrix_eq_repr_mul, ← hb, ← map_mul, h]

end NormMap

namespace AdeleBaseChange

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

variable (K L) in

def adeleTensorAlgEquivLeft : 𝔸[K] ⊗[K] L ≃ₐ[𝔸[K]] 𝔸[L] :=
  AlgEquiv.ofRingEquiv
    (f := (Algebra.TensorProduct.comm K 𝔸[K] L).toRingEquiv.trans
      (adeleTensorEquiv K L).toRingEquiv) fun a ↦ by
    change adeleTensorEquiv K L (Algebra.TensorProduct.comm K 𝔸[K] L (a ⊗ₜ 1)) = adeleMap K L a
    rw [Algebra.TensorProduct.comm_tmul, adeleTensorEquiv_tmul, map_one, one_mul]

theorem adeleTensorAlgEquivLeft_tmul (a : 𝔸[K]) (l : L) :
    adeleTensorAlgEquivLeft K L (a ⊗ₜ l) = algebraMap L 𝔸[L] l * adeleMap K L a := by
  change adeleTensorEquiv K L (Algebra.TensorProduct.comm K 𝔸[K] L (a ⊗ₜ l)) = _
  rw [Algebra.TensorProduct.comm_tmul, adeleTensorEquiv_tmul]

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι K L)

def adeleBasis : Basis ι 𝔸[K] 𝔸[L] :=
  (Algebra.TensorProduct.basis 𝔸[K] b).map (adeleTensorAlgEquivLeft K L).toLinearEquiv

omit [Fintype ι] [DecidableEq ι] in
theorem adeleBasis_apply (i : ι) : adeleBasis b i = algebraMap L 𝔸[L] (b i) := by
  rw [adeleBasis, Basis.map_apply, Algebra.TensorProduct.basis_apply]
  change adeleTensorAlgEquivLeft K L (1 ⊗ₜ b i) = _
  rw [adeleTensorAlgEquivLeft_tmul, map_one, mul_one]

theorem adeleBasis_repr (y : 𝔸[L]) (i : ι) : (adeleBasis b).repr y i = coord b i y := by
  have hy : ∑ j, coord b j y • adeleBasis b j = y := by
    conv_rhs => rw [← adeleTensorEquiv_sum_coord b y]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [adeleTensorEquiv_tmul, adeleBasis_apply, Algebra.smul_def, algebraMap_adeleRing, mul_comm]
  conv_lhs => rw [← hy]
  rw [Basis.repr_sum_self]

omit [DecidableEq ι] in

theorem adeleBasis_repr_algebraMap (l : L) (i : ι) :
    (adeleBasis b).repr (algebraMap L 𝔸[L] l) i = algebraMap K 𝔸[K] (b.repr l i) := by
  classical
  have hl : algebraMap L 𝔸[L] l = ∑ j, algebraMap K 𝔸[K] (b.repr l j) • adeleBasis b j := by
    conv_lhs => rw [← b.sum_repr l]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [adeleBasis_apply, Algebra.smul_def, map_mul, Algebra.smul_def, algebraMap_adeleRing,
      adeleMap_algebraMap]
  rw [hl, Basis.repr_sum_self]

variable (K) in

scoped instance nontrivial_adeleRing : Nontrivial 𝔸[K] :=
  (AdeleRing.algebraMap_injective (𝓞 K) K).nontrivial

variable (K L) in
scoped instance : Module.Free 𝔸[K] 𝔸[L] := .of_basis (adeleBasis (Module.finBasis K L))

variable (K L) in
scoped instance : Module.Finite 𝔸[K] 𝔸[L] := .of_basis (adeleBasis (Module.finBasis K L))

variable (K L) in

theorem finrank_adeleRing : Module.finrank 𝔸[K] 𝔸[L] = Module.finrank K L := by
  rw [Module.finrank_eq_card_basis (adeleBasis (Module.finBasis K L)), Fintype.card_fin]

theorem continuous_norm_adeleRing :
    Continuous (Algebra.norm 𝔸[K] : 𝔸[L] → 𝔸[K]) := by
  let b := Module.finBasis K L
  have h : (Algebra.norm 𝔸[K] : 𝔸[L] → 𝔸[K]) =
      fun y ↦ (Algebra.leftMulMatrix (adeleBasis b) y).det :=
    funext fun y ↦ Algebra.norm_eq_matrix_det (adeleBasis b) y
  rw [h]
  refine Continuous.matrix_det (continuous_matrix fun i j ↦ ?_)
  simp_rw [Algebra.leftMulMatrix_eq_repr_mul, adeleBasis_repr]
  exact (continuous_coord b i).comp (continuous_id.mul continuous_const)

theorem norm_adeleRing_algebraMap (l : L) :
    Algebra.norm 𝔸[K] (algebraMap L 𝔸[L] l) = algebraMap K 𝔸[K] (Algebra.norm K l) := by
  classical
  exact norm_map_of_repr (algebraMap K 𝔸[K]) (algebraMap L 𝔸[L]) (Module.finBasis K L)
    (adeleBasis (Module.finBasis K L)) (fun y i ↦ adeleBasis_repr_algebraMap _ y i) l

theorem norm_adeleRing_adeleMap (x : 𝔸[K]) :
    Algebra.norm 𝔸[K] (adeleMap K L x) = x ^ Module.finrank K L := by
  rw [← finrank_adeleRing K L]
  exact Algebra.norm_algebraMap x

theorem adeleRetraction_algebraMap (l : L) :
    adeleRetraction K L (algebraMap L 𝔸[L] l) = algebraMap K 𝔸[K] (normalizedTrace K L l) := by
  have h : (adeleTensorEquiv K L).symm (algebraMap L 𝔸[L] l) = l ⊗ₜ 1 := by
    rw [AlgEquiv.symm_apply_eq, adeleTensorEquiv_tmul, map_one, mul_one]
  rw [adeleRetraction, h]
  change TensorProduct.lid K 𝔸[K] (LinearMap.rTensor 𝔸[K] (normalizedTrace K L) (l ⊗ₜ 1)) = _
  rw [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, Algebra.algebraMap_eq_smul_one]

end AdeleBaseChange

open AdeleBaseChange

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

def ideleEmbedding : IdeleGroup K →* IdeleGroup L :=
  Units.map (adeleMap K L).toMonoidHom

variable {K L}

@[simp]
theorem coe_ideleEmbedding (x : IdeleGroup K) :
    ((ideleEmbedding K L x : IdeleGroup L) : 𝔸[L]) = adeleMap K L x :=
  rfl

theorem ideleEmbedding_injective : Function.Injective (ideleEmbedding K L) := fun _ _ h ↦
  Units.ext (adeleMap_injective (congrArg Units.val h))

theorem continuous_ideleEmbedding : Continuous (ideleEmbedding K L) :=
  Continuous.units_map (adeleMap K L).toMonoidHom continuous_adeleMap

theorem isClosedEmbedding_ideleEmbedding : IsClosedEmbedding (ideleEmbedding K L) :=
  haveI : T2Space (FiniteAdeleRing (𝓞 L) L) := inferInstanceAs (T2Space
    (Πʳ w : HeightOneSpectrum (𝓞 L), [w.adicCompletion L, w.adicCompletionIntegers L]))
  haveI : T2Space (InfiniteAdeleRing L) :=
    inferInstanceAs (T2Space ((w : NumberField.InfinitePlace L) → w.Completion))
  haveI : T2Space 𝔸[L] := inferInstanceAs (T2Space (InfiniteAdeleRing L × FiniteAdeleRing (𝓞 L) L))
  haveI : T2Space (FiniteAdeleRing (𝓞 K) K) := inferInstanceAs (T2Space
    (Πʳ v : HeightOneSpectrum (𝓞 K), [v.adicCompletion K, v.adicCompletionIntegers K]))
  haveI : T2Space (InfiniteAdeleRing K) :=
    inferInstanceAs (T2Space ((v : NumberField.InfinitePlace K) → v.Completion))
  haveI : T2Space 𝔸[K] := inferInstanceAs (T2Space (InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K))
  Topology.IsClosedEmbedding.units_map (f := (adeleMap K L).toMonoidHom) isClosedEmbedding_adeleMap

theorem ideleEmbedding_diagonal (k : Kˣ) :
    ideleEmbedding K L (IdeleGroup.diagonal K k) =
      IdeleGroup.diagonal L (Units.map (algebraMap K L).toMonoidHom k) :=
  Units.ext (adeleMap_algebraMap (k : K))

variable (K L) in

def ideleNorm : IdeleGroup L →* IdeleGroup K :=
  Units.map (Algebra.norm 𝔸[K] : 𝔸[L] →* 𝔸[K])

@[simp]
theorem coe_ideleNorm (x : IdeleGroup L) :
    ((ideleNorm K L x : IdeleGroup K) : 𝔸[K]) = Algebra.norm 𝔸[K] (x : 𝔸[L]) :=
  rfl

theorem continuous_ideleNorm : Continuous (ideleNorm K L) :=
  Continuous.units_map _ continuous_norm_adeleRing

theorem ideleNorm_diagonal (l : Lˣ) :
    ideleNorm K L (IdeleGroup.diagonal L l) =
      IdeleGroup.diagonal K (Units.map (Algebra.norm K : L →* K) l) :=
  Units.ext (norm_adeleRing_algebraMap (l : L))

theorem ideleNorm_ideleEmbedding (x : IdeleGroup K) :
    ideleNorm K L (ideleEmbedding K L x) = x ^ Module.finrank K L :=
  Units.ext (by rw [Units.val_pow_eq_pow_val]; exact norm_adeleRing_adeleMap (x : 𝔸[K]))

theorem diagonal_range_le_comap_ideleEmbedding :
    (IdeleGroup.diagonal K).range ≤ (IdeleGroup.diagonal L).range.comap (ideleEmbedding K L) := by
  rintro _ ⟨k, rfl⟩
  exact ⟨Units.map (algebraMap K L).toMonoidHom k, (ideleEmbedding_diagonal k).symm⟩

theorem diagonal_range_le_comap_ideleNorm :
    (IdeleGroup.diagonal L).range ≤ (IdeleGroup.diagonal K).range.comap (ideleNorm K L) := by
  rintro _ ⟨l, rfl⟩
  exact ⟨Units.map (Algebra.norm K : L →* K) l, (ideleNorm_diagonal l).symm⟩

variable (K L) in

def ideleClassMap : IdeleClassGroup K →* IdeleClassGroup L :=
  QuotientGroup.map _ _ (ideleEmbedding K L) diagonal_range_le_comap_ideleEmbedding

variable (K L) in

def ideleClassNorm : IdeleClassGroup L →* IdeleClassGroup K :=
  QuotientGroup.map _ _ (ideleNorm K L) diagonal_range_le_comap_ideleNorm

@[simp]
theorem ideleClassMap_mk (x : IdeleGroup K) :
    ideleClassMap K L (IdeleClassGroup.mk K x) = IdeleClassGroup.mk L (ideleEmbedding K L x) :=
  rfl

@[simp]
theorem ideleClassNorm_mk (x : IdeleGroup L) :
    ideleClassNorm K L (IdeleClassGroup.mk L x) = IdeleClassGroup.mk K (ideleNorm K L x) :=
  rfl

theorem continuous_ideleClassMap : Continuous (ideleClassMap K L) :=
  (QuotientGroup.isQuotientMap_mk _).continuous_iff.2
    ((IdeleClassGroup.continuous_mk L).comp continuous_ideleEmbedding)

theorem continuous_ideleClassNorm : Continuous (ideleClassNorm K L) :=
  (QuotientGroup.isQuotientMap_mk _).continuous_iff.2
    ((IdeleClassGroup.continuous_mk K).comp continuous_ideleNorm)

theorem ideleClassNorm_ideleClassMap (c : IdeleClassGroup K) :
    ideleClassNorm K L (ideleClassMap K L c) = c ^ Module.finrank K L := by
  obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective K c
  rw [ideleClassMap_mk, ideleClassNorm_mk, ideleNorm_ideleEmbedding, map_pow]

theorem mem_range_diagonal_of_ideleEmbedding {x : IdeleGroup K}
    (hx : ideleEmbedding K L x ∈ (IdeleGroup.diagonal L).range) :
    x ∈ (IdeleGroup.diagonal K).range := by
  obtain ⟨l, hl⟩ := hx
  have hxk : (x : 𝔸[K]) = algebraMap K 𝔸[K] (normalizedTrace K L (l : L)) := by
    rw [← adeleRetraction_adeleMap (L := L) (x : 𝔸[K]), ← coe_ideleEmbedding, ← hl,
      IdeleGroup.coe_diagonal, adeleRetraction_algebraMap]
  have hk : normalizedTrace K L (l : L) ≠ 0 := by
    intro h
    rw [h, map_zero] at hxk
    exact x.ne_zero hxk
  exact ⟨Units.mk0 _ hk, Units.ext hxk.symm⟩

theorem ideleClassMap_injective : Function.Injective (ideleClassMap K L) := by
  refine (injective_iff_map_eq_one _).2 fun c hc ↦ ?_
  obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective K c
  rw [ideleClassMap_mk, ← MonoidHom.mem_ker, IdeleClassGroup.ker_mk] at hc
  rw [← MonoidHom.mem_ker, IdeleClassGroup.ker_mk]
  exact mem_range_diagonal_of_ideleEmbedding hc

end

end GroundTheory.Global
