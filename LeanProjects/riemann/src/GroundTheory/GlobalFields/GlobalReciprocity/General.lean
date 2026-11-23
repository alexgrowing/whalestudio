import Mathlib
import GroundTheory.GlobalFields.GlobalReciprocity.RangeDiagonalLeKerIdeleSymbol
import GroundTheory.GlobalFields.NormResidueSymbol.Functorial

namespace GroundTheory.Global

open IsDedekindDomain NumberField IntermediateField IdeleGroup AdeleBaseChange

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

namespace FiniteSubfield

variable {F E : FiniteSubfield} [Fact (F ≤ E)]

theorem apply_mem_of_normal_field [Normal F.1 E.1] {g : ℚ̄ ≃ₐ[ℚ] ℚ̄} (hg : g ∈ F.1.fixingSubgroup)
    {x : ℚ̄} (hx : x ∈ E.1) : g x ∈ E.1 := by
  let g' : ℚ̄ ≃ₐ[F.1] ℚ̄ := IntermediateField.fixingSubgroupEquiv F.1 ⟨g, hg⟩
  have : IsScalarTower F.1 E.1 ℚ̄ := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have h := AlgEquiv.restrictNormal_commutes g' E.1 ⟨x, hx⟩
  have e : g' x = g x := rfl
  rw [← e, ← show algebraMap E.1 ℚ̄ ⟨x, hx⟩ = x from rfl, ← h]
  exact (g'.restrictNormal E.1 ⟨x, hx⟩).2

theorem normal_subgroupOf_of_isGalois [IsGalois F.1 E.1] :
    (E.1.fixingSubgroup.subgroupOf F.1.fixingSubgroup).Normal := by
  refine ⟨fun l hl g ↦ ?_⟩
  rw [Subgroup.mem_subgroupOf, IntermediateField.mem_fixingSubgroup_iff] at hl ⊢
  intro x hx
  have hy : ((g⁻¹ : F.1.fixingSubgroup) : ℚ̄ ≃ₐ[ℚ] ℚ̄) x ∈ E.1 :=
    apply_mem_of_normal_field (g⁻¹ : F.1.fixingSubgroup).2 hx
  change (g : ℚ̄ ≃ₐ[ℚ] ℚ̄) ((l : ℚ̄ ≃ₐ[ℚ] ℚ̄) (((g⁻¹ : F.1.fixingSubgroup) : ℚ̄ ≃ₐ[ℚ] ℚ̄) x)) = x
  rw [hl _ hy, ← AlgEquiv.mul_apply, ← Subgroup.coe_mul, mul_inv_cancel]
  rfl

end FiniteSubfield

section Transfer

variable {K K' L L' : Type*} [Field K] [NumberField K] [Field K'] [NumberField K'] [Field L]
  [NumberField L] [Field L'] [NumberField L'] [Algebra K K'] [Algebra K L] [Algebra K L']
  [Algebra K' L'] [Algebra L L'] [IsScalarTower K K' L'] [IsScalarTower K L L']

omit [NumberField K] [NumberField K'] in

theorem finrank_eq_one_of_bijective (hK : Function.Bijective (algebraMap K K')) :
    Module.finrank K K' = 1 :=
  (AlgEquiv.ofBijective (Algebra.ofId K K') hK).toLinearEquiv.finrank_eq.symm.trans
    (Module.finrank_self K)

omit [Algebra K L] [Algebra K L'] [Algebra K' L'] [Algebra L L'] [IsScalarTower K K' L']
  [IsScalarTower K L L'] in

theorem ideleNorm_ideleEmbedding_of_bijective (hK : Function.Bijective (algebraMap K K'))
    (x : IdeleGroup K) : ideleNorm K K' (ideleEmbedding K K' x) = x := by
  rw [ideleNorm_ideleEmbedding, finrank_eq_one_of_bijective hK, pow_one]

variable [IsGalois K L]

omit [NumberField K] [NumberField K'] [NumberField L] [NumberField L'] in

theorem restrictNormal_restrictScalars_eq_one (hL : Function.Bijective (algebraMap L L'))
    {σ : L' ≃ₐ[K'] L'} (h : (σ.restrictScalars K).restrictNormal L = 1) : σ = 1 := by
  refine AlgEquiv.ext fun y ↦ ?_
  obtain ⟨l, rfl⟩ := hL.2 y
  have e := AlgEquiv.restrictNormal_commutes (σ.restrictScalars K) L l
  rw [h, AlgEquiv.one_apply] at e
  exact e.symm

variable [IsMulCommutative (L ≃ₐ[K] L)] [IsGalois K' L'] [IsMulCommutative (L' ≃ₐ[K'] L')]

theorem ideleSymbol_diagonal_of_bijective (hK : Function.Bijective (algebraMap K K'))
    (hA : ∀ a : K'ˣ, ideleSymbol K' L' (diagonal K' a) = 1) (a : Kˣ) :
    ideleSymbol K L (diagonal K a) = 1 := by
  rw [← ideleNorm_ideleEmbedding_of_bijective hK (diagonal K a),
    ← restrictNormal_restrictScalars_ideleSymbol (L := L) (L' := L'), ideleEmbedding_diagonal, hA]
  exact map_one ((AlgEquiv.restrictNormalHom (F := K) (K₁ := L') L).comp (restrictScalarsHom K))

theorem ker_ideleSymbol_le_of_bijective (hK : Function.Bijective (algebraMap K K'))
    (hL : Function.Bijective (algebraMap L L'))
    (hker : (ideleSymbol K' L').ker ≤ (diagonal K').range ⊔ (ideleNorm K' L').range) :
    (ideleSymbol K L).ker ≤ (diagonal K).range ⊔ (ideleNorm K L).range := by
  intro x hx
  have h1 : ideleSymbol K' L' (ideleEmbedding K K' x) = 1 := by
    refine restrictNormal_restrictScalars_eq_one (K := K) hL ?_
    rw [restrictNormal_restrictScalars_ideleSymbol, ideleNorm_ideleEmbedding_of_bijective hK]
    exact hx
  have hmap : ((diagonal K').range ⊔ (ideleNorm K' L').range).map (ideleNorm K K') ≤
      (diagonal K).range ⊔ (ideleNorm K L).range := by
    rw [Subgroup.map_sup]
    refine sup_le_sup ?_ ?_
    · rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
      exact ⟨_, (ideleNorm_diagonal b).symm⟩
    · rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
      exact ⟨ideleNorm L L' y, by rw [ideleNorm_ideleNorm, ideleNorm_ideleNorm]⟩
  rw [← ideleNorm_ideleEmbedding_of_bijective hK x]
  exact hmap ⟨_, hker h1, rfl⟩

end Transfer

section Embedding

def rangeMap {A : Type*} [Field A] [Algebra ℚ A] (f : A →ₐ[ℚ] ℚ̄) : A →+* f.fieldRange where
  toFun a := ⟨f a, a, rfl⟩
  map_one' := Subtype.ext (map_one f)
  map_mul' a b := Subtype.ext (map_mul f a b)
  map_zero' := Subtype.ext (map_zero f)
  map_add' a b := Subtype.ext (map_add f a b)

theorem rangeMap_bijective {A : Type*} [Field A] [Algebra ℚ A] (f : A →ₐ[ℚ] ℚ̄) :
    Function.Bijective (rangeMap f) :=
  ⟨(rangeMap f).injective, by rintro ⟨_, a, rfl⟩; exact ⟨a, rfl⟩⟩

theorem finiteDimensional_fieldRange {A : Type*} [Field A] [NumberField A] (f : A →ₐ[ℚ] ℚ̄) :
    FiniteDimensional ℚ f.fieldRange :=
  Module.Finite.of_surjective
    ({ toFun := rangeMap f, map_add' := map_add _, map_smul' := fun c a ↦ Subtype.ext (f.toLinearMap.map_smul c a) } :
      A →ₗ[ℚ] f.fieldRange) (rangeMap_bijective f).2

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

def embedding : L →ₐ[ℚ] ℚ̄ := IsAlgClosed.lift

def baseEmbedding : K →ₐ[ℚ] ℚ̄ := (embedding L).comp (IsScalarTower.toAlgHom ℚ K L)

def topField : FiniteSubfield := ⟨(embedding L).fieldRange, finiteDimensional_fieldRange _⟩

def baseField : FiniteSubfield := ⟨(baseEmbedding K L).fieldRange, finiteDimensional_fieldRange _⟩

instance fact_baseField_le : Fact (baseField K L ≤ topField L) :=
  ⟨by
    rintro _ ⟨k, rfl⟩
    exact ⟨algebraMap K L k, rfl⟩⟩

variable {K L} [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]

theorem ideleSymbol_diagonal_and_ker_le :
    (∀ a : Kˣ, ideleSymbol K L (diagonal K a) = 1) ∧
      (ideleSymbol K L).ker ≤ (diagonal K).range ⊔ (ideleNorm K L).range := by
  let K' := baseField K L
  let L' := topField L
  let _ : Algebra K K'.1 := (rangeMap (baseEmbedding K L)).toAlgebra
  let _ : Algebra L L'.1 := (rangeMap (embedding L)).toAlgebra
  let _ : Algebra K L'.1 := ((rangeMap (embedding L)).comp (algebraMap K L)).toAlgebra
  have : IsScalarTower K K'.1 L'.1 := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower K L L'.1 := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hK : Function.Bijective (algebraMap K K'.1) := rangeMap_bijective _
  have hL : Function.Bijective (algebraMap L L'.1) := rangeMap_bijective _
  have : IsGalois K L'.1 :=
    IsGalois.of_algEquiv (AlgEquiv.ofBijective (IsScalarTower.toAlgHom K L L'.1) hL)
  have : IsGalois K'.1 L'.1 := IsGalois.tower_top_of_isGalois K K'.1 L'.1
  have : IsMulCommutative (L'.1 ≃ₐ[K'.1] L'.1) := by
    refine ⟨⟨fun σ τ ↦ ?_⟩⟩
    let f := (AlgEquiv.restrictNormalHom (F := K) (K₁ := L'.1) L).comp (restrictScalarsHom (K' := K'.1) (L' := L'.1) K)
    have h := restrictNormal_restrictScalars_eq_one (K := K) (K' := K'.1) (L := L) (L' := L'.1) hL
      (σ := σ * τ * (τ * σ)⁻¹) (by
      change f (σ * τ * (τ * σ)⁻¹) = 1
      rw [map_mul, map_inv, map_mul, map_mul, mul_comm' (f σ) (f τ), mul_inv_cancel])
    rwa [mul_inv_eq_one] at h
  have := FiniteSubfield.normal_subgroupOf_of_isGalois (F := K') (E := L')
  exact ⟨ideleSymbol_diagonal_of_bijective hK (IdeleClassLimit.ideleSymbol_diagonal K' L'),
    ker_ideleSymbol_le_of_bijective hK hL (IdeleClassLimit.ker_ideleSymbol K' L').le⟩

end Embedding

section Reciprocity

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]

theorem ideleSymbol_diagonal (a : Kˣ) : ideleSymbol K L (diagonal K a) = 1 :=
  ideleSymbol_diagonal_and_ker_le.1 a

theorem diagonal_range_le_ker_ideleSymbol : (diagonal K).range ≤ (ideleSymbol K L).ker := by
  rintro _ ⟨a, rfl⟩
  exact ideleSymbol_diagonal a

theorem ker_ideleSymbol : (ideleSymbol K L).ker = (diagonal K).range ⊔ (ideleNorm K L).range :=
  le_antisymm ideleSymbol_diagonal_and_ker_le.2
    (sup_le diagonal_range_le_ker_ideleSymbol (range_ideleNorm_le_ker_ideleSymbol L))

omit [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] in

instance ideleClassNorm_range_normal : (ideleClassNorm K L).range.Normal :=
  ⟨fun n hn g ↦ by rwa [mul_comm g n, mul_inv_cancel_right]⟩

variable (K L) in

def reciprocityMap : IdeleClassGroup K →* (L ≃ₐ[K] L) :=
  QuotientGroup.lift _ (ideleSymbol K L) diagonal_range_le_ker_ideleSymbol

@[simp]
theorem reciprocityMap_mk (x : IdeleGroup K) :
    reciprocityMap K L (IdeleClassGroup.mk K x) = ideleSymbol K L x :=
  rfl

theorem continuous_reciprocityMap : Continuous (reciprocityMap K L) :=
  (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 (continuous_ideleSymbol L)

theorem ker_reciprocityMap : (reciprocityMap K L).ker = (ideleClassNorm K L).range := by
  ext c
  obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective K c
  rw [MonoidHom.mem_ker, reciprocityMap_mk, ← MonoidHom.mem_ker, ker_ideleSymbol]
  constructor
  · intro hx
    obtain ⟨d, hd, n, hn, rfl⟩ := Subgroup.mem_sup.1 hx
    obtain ⟨y, rfl⟩ := hn
    obtain ⟨a, rfl⟩ := hd
    refine ⟨IdeleClassGroup.mk L y, ?_⟩
    rw [ideleClassNorm_mk, map_mul, IdeleClassGroup.mk_diagonal]
    exact (one_mul (IdeleClassGroup.mk K (ideleNorm K L y))).symm
  · rintro ⟨c', hc'⟩
    obtain ⟨y, rfl⟩ := IdeleClassGroup.mk_surjective L c'
    rw [ideleClassNorm_mk] at hc'
    have hd : (ideleNorm K L y)⁻¹ * x ∈ (diagonal K).range := by
      rw [← IdeleClassGroup.ker_mk, MonoidHom.mem_ker, map_mul, map_inv, hc', inv_mul_cancel]
    rw [← mul_inv_cancel_left (ideleNorm K L y) x]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ⟨y, rfl⟩) (Subgroup.mem_sup_left hd)

end Reciprocity

universe u

section Isomorphism

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]

theorem reciprocityMap_surjective : Function.Surjective (reciprocityMap K L) := fun σ ↦
  let ⟨x, hx⟩ := ideleSymbol_surjective (K := K) (L := L) σ
  ⟨IdeleClassGroup.mk K x, hx⟩

variable (K L) in

def reciprocityMapEquiv : IdeleClassGroup K ⧸ (ideleClassNorm K L).range ≃* (L ≃ₐ[K] L) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_reciprocityMap (K := K) (L := L)).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ reciprocityMap_surjective)

@[simp]
theorem reciprocityMapEquiv_mk (x : IdeleGroup K) :
    reciprocityMapEquiv K L (QuotientGroup.mk (IdeleClassGroup.mk K x)) = ideleSymbol K L x :=
  rfl

theorem index_range_ideleClassNorm_eq_finrank_of_isMulCommutative : (ideleClassNorm K L).range.index = Module.finrank K L := by
  rw [Subgroup.index, Nat.card_congr (reciprocityMapEquiv K L).toEquiv, IsGalois.card_aut_eq_finrank]

end Isomorphism

end

end GroundTheory.Global
