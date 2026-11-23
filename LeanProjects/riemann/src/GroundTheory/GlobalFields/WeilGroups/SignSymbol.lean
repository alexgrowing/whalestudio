import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.SymbolBridgeSum
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.OpenSubgroups
import GroundTheory.GlobalFields.GlobalArtinMap.Kernel
import GroundTheory.GlobalFields.NormResidueSymbol.RestrictNormalInfiniteLocalSymbol
set_option maxSynthPendingDepth 1

namespace GroundTheory.Global

open NumberField IntermediateField IsDedekindDomain IdeleGroup FiniteSubfield GroundTheory.ProfCoh GroundTheory.LocalField

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

section Transport

variable {K : Type*} [Field K] [NumberField K] {L L' : Type*} [Field L] [NumberField L] [Field L']
  [NumberField L'] [Algebra K L] [Algebra K L'] [IsGalois K L] [IsGalois K L']
  [IsMulCommutative (L ≃ₐ[K] L)] [IsMulCommutative (L' ≃ₐ[K] L')]

theorem ideleSymbol_apply_algEquiv (e : L ≃ₐ[K] L') (x : IdeleGroup K) (l : L) :
    ideleSymbol K L' x (e l) = e (ideleSymbol K L x l) := by
  let _ : Algebra L L' := e.toRingHom.toAlgebra
  have : IsScalarTower K L L' := IsScalarTower.of_algebraMap_eq fun a ↦ (e.commutes a).symm
  have h := AlgEquiv.restrictNormal_commutes (ideleSymbol K L' x) L l
  rw [restrictNormal_ideleSymbol L L' x] at h
  exact h.symm

end Transport

section Bridge

variable {K : FiniteSubfield} (E : FiniteSubfield) [hKE : Fact (K ≤ E)]

abbrev overField (K E : FiniteSubfield) [hKE : Fact (K ≤ E)] : IntermediateField K.1 ℚ̄ :=
  extendScalars (show K.1 ≤ E.1 from hKE.out)

def overFieldEquiv (K E : FiniteSubfield) [Fact (K ≤ E)] : E.1 ≃ₐ[K.1] ↥(overField K E) :=
  AlgEquiv.ofRingEquiv (f :=
    { toFun := fun y ↦ ⟨(y : ℚ̄), y.2⟩
      invFun := fun y ↦ ⟨(y : ℚ̄), y.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl
      map_add' := fun _ _ ↦ rfl }) fun _ ↦ rfl

@[simp]
theorem coe_overFieldEquiv (y : E.1) : ((overFieldEquiv K E y : ↥(overField K E)) : ℚ̄) = (y : ℚ̄) :=
  rfl

variable [(E.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup).Normal] [IsMulCommutative (E.1 ≃ₐ[K.1] E.1)]

attribute [local instance] FiniteSubfield.isGalois_of_normal

instance : FiniteDimensional K.1 ↥(overField K E) :=
  LinearEquiv.finiteDimensional (overFieldEquiv K E).toLinearEquiv

instance : IsGalois K.1 ↥(overField K E) := IsGalois.of_algEquiv (overFieldEquiv K E)

instance : IsMulCommutative (↥(overField K E) ≃ₐ[K.1] ↥(overField K E)) :=
  ⟨⟨fun σ τ ↦ by
    apply (AlgEquiv.autCongr (overFieldEquiv K E)).symm.injective
    simp only [map_mul]
    exact mul_comm' _ _⟩⟩

instance : IsAbelianGalois K.1 ↥(overField K E) := ⟨⟩

theorem restrictHom_eq_ideleSymbol_of_artinMap (x : IdeleGroup K.1) (g : K.1.fixingSubgroup)
    (hg : ∀ (y : ℚ̄) (hy : y ∈ maximalAbelianExtension K.1 ℚ̄),
      (g : ℚ̄ ≃ₐ[ℚ] ℚ̄) y = (artinMap K.1 ℚ̄ (IdeleClassGroup.mk K.1 x) ⟨y, hy⟩ : ℚ̄)) :
    restrictHom (E := E) g = ideleSymbol K.1 E.1 x := by
  refine AlgEquiv.ext fun l ↦ Subtype.ext ?_
  rw [FiniteSubfield.coe_restrictHom_apply]
  have hl : (l : ℚ̄) ∈ maximalAbelianExtension K.1 ℚ̄ :=
    le_maximalAbelianExtension (overField K E) (overFieldEquiv K E l).2
  rw [hg _ hl]
  have h := artinMap_apply (overField K E) (IdeleClassGroup.mk K.1 x) (overFieldEquiv K E l)
  refine h.trans ?_
  rw [reciprocityMap_mk, ideleSymbol_apply_algEquiv (overFieldEquiv K E) x l, coe_overFieldEquiv]

end Bridge

variable {K : FiniteSubfield} (ι : LocalEmbeddings K)

def ideleLocalSymbolAt : Place K.1 → IdeleGroup K.1 → K.1.fixingSubgroup
  | .inr v, x => globalDecomp (v.adicCompletion K.1) (ι.fin v)
      ((localArtinMap (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))
        (finiteProj v x)).liftNormal (AlgebraicClosure (v.adicCompletion K.1)))
  | .inl v, x => globalDecomp v.Completion (ι.inf v)
      (exists_eq_one_iff_mem_range_norm v (infiniteProj v x : v.Completion)).choose

section Symbols

variable (E : FiniteSubfield) [Fact (K ≤ E)]
  [(E.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup).Normal] [IsMulCommutative (E.1 ≃ₐ[K.1] E.1)]

attribute [local instance] FiniteSubfield.isGalois_of_normal galCommGroup

theorem restrictHom_ideleLocalSymbolAt_inr (v : HeightOneSpectrum (𝓞 K.1)) (x : IdeleGroup K.1) :
    restrictHom (E := E) (ideleLocalSymbolAt ι (.inr v) x) = localSymbol E.1 v (finiteProj v x) :=
  restrictHom_globalDecomp_of_finite E (ι.fin v) fun y hy ↦
    AlgEquiv.liftNormal_commutes _ _ (⟨y, hy⟩ : maximalAbelianExtension
      (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1)))

theorem restrictHom_ideleLocalSymbolAt_inl (v : InfinitePlace K.1) (x : IdeleGroup K.1) :
    restrictHom (E := E) (ideleLocalSymbolAt ι (.inl v) x) = infiniteLocalSymbol E.1 v (infiniteProj v x) :=
  restrictHom_globalDecomp_of_infinite E (ι.inf v)
    (exists_eq_one_iff_mem_range_norm v (infiniteProj v x : v.Completion)).choose_spec

theorem finsum_char_ideleLocalSymbolAt_eq (χ : Additive K.1.fixingSubgroup →ₜ+ QZ)
    (hχ : ∀ h : K.1.fixingSubgroup, (h : ℚ̄ ≃ₐ[ℚ] ℚ̄) ∈ E.1.fixingSubgroup → χ (Additive.ofMul h) = 0)
    (x : IdeleGroup K.1) (g : K.1.fixingSubgroup) (hg : restrictHom (E := E) g = ideleSymbol K.1 E.1 x) :
    ∑ᶠ v : Place K.1, χ (Additive.ofMul (ideleLocalSymbolAt ι v x)) = χ (Additive.ofMul g) := by
  classical
  set R := (restrictHom : K.1.fixingSubgroup →* (E.1 ≃ₐ[K.1] E.1)) with hR
  set χm : K.1.fixingSubgroup →* Multiplicative QZ :=
    AddMonoidHom.toMultiplicativeRight χ.toAddMonoidHom with hχm
  have hχm_apply : ∀ h, χ (Additive.ofMul h) = Multiplicative.toAdd (χm h) := fun _ ↦ rfl
  have hker : R.ker ≤ χm.ker := by
    intro h hh
    rw [hR, FiniteSubfield.ker_restrictHom, Subgroup.mem_subgroupOf] at hh
    rw [MonoidHom.mem_ker, ← ofAdd_toAdd (χm h), ← hχm_apply, hχ h hh, ofAdd_zero]
  set χ' := R.liftOfSurjective restrictHom_surjective ⟨χm, hker⟩ with hχ'
  have hχ'R : ∀ h, χ' (R h) = χm h := fun h ↦
    R.liftOfRightInverse_comp_apply _ (Function.rightInverse_surjInv restrictHom_surjective) ⟨χm, hker⟩ h
  have hF_inr : ∀ v, χ (Additive.ofMul (ideleLocalSymbolAt ι (.inr v) x)) =
      Multiplicative.toAdd (χ' (localSymbol E.1 v (finiteProj v x))) := by
    intro v
    rw [hχm_apply, ← hχ'R, hR, restrictHom_ideleLocalSymbolAt_inr]
  have hF_inl : ∀ w, χ (Additive.ofMul (ideleLocalSymbolAt ι (.inl w) x)) =
      Multiplicative.toAdd (χ' (infiniteLocalSymbol E.1 w (infiniteProj w x))) := by
    intro w
    rw [hχm_apply, ← hχ'R, hR, restrictHom_ideleLocalSymbolAt_inl]
  obtain ⟨S, hS⟩ : ∃ S : Finset (HeightOneSpectrum (𝓞 K.1)),
      Function.mulSupport (fun v ↦ localSymbol E.1 v (finiteProj v x)) ⊆ S :=
    ⟨(hasFiniteMulSupport_localSymbol E.1 x).toFinset, fun v hv ↦ (Set.Finite.mem_toFinset _).2 hv⟩
  have hψ : ideleSymbol K.1 E.1 x = (∏ v ∈ S, localSymbol E.1 v (finiteProj v x)) *
      ∏ w, infiniteLocalSymbol E.1 w (infiniteProj w x) := by
    rw [ideleSymbol_apply, finprod_eq_prod_of_mulSupport_subset _ hS]
  have hsupp : Function.support (fun v : Place K.1 ↦ χ (Additive.ofMul (ideleLocalSymbolAt ι v x))) ⊆
      (Finset.univ.disjSum S : Finset (Place K.1)) := by
    rintro (w | v) hv
    · exact Finset.inl_mem_disjSum.2 (Finset.mem_univ w)
    · refine Finset.inr_mem_disjSum.2 (hS ?_)
      intro h1
      apply hv
      change χ (Additive.ofMul (ideleLocalSymbolAt ι (.inr v) x)) = 0
      rw [hF_inr, show localSymbol E.1 v (finiteProj v x) = 1 from h1, map_one, toAdd_one]
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_disjSum, hχm_apply, ← hχ'R, hg, hψ, map_mul,
    toAdd_mul, map_prod χ', map_prod χ', toAdd_prod, toAdd_prod, add_comm]
  congr 1
  · exact Finset.sum_congr rfl fun v _ ↦ hF_inr v
  · exact Finset.sum_congr rfl fun w _ ↦ hF_inl w

end Symbols

theorem finsum_char_ideleLocalSymbolAt_eq_of_artinMap (χ : Additive K.1.fixingSubgroup →ₜ+ QZ)
    (x : IdeleGroup K.1) (g : K.1.fixingSubgroup)
    (hg : ∀ (y : ℚ̄) (hy : y ∈ maximalAbelianExtension K.1 ℚ̄),
      (g : ℚ̄ ≃ₐ[ℚ] ℚ̄) y = (artinMap K.1 ℚ̄ (IdeleClassGroup.mk K.1 x) ⟨y, hy⟩ : ℚ̄)) :
    ∑ᶠ v : Place K.1, χ (Additive.ofMul (ideleLocalSymbolAt ι v x)) = χ (Additive.ofMul g) := by
  let U : OpenSubgroup K.1.fixingSubgroup := (charKerOpen χ).toOpenSubgroup
  let E := fieldOf U
  have hEU : E.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup = (U : Subgroup K.1.fixingSubgroup) :=
    subgroupOf_fieldOf U
  have hmem : ∀ h : K.1.fixingSubgroup, (h : ℚ̄ ≃ₐ[ℚ] ℚ̄) ∈ E.1.fixingSubgroup ↔ χ (Additive.ofMul h) = 0 := by
    intro h
    rw [← Subgroup.mem_subgroupOf, hEU]
    change h ∈ charKer (charAdd χ) ↔ _
    rw [mem_charKer]
    exact ⟨fun h' ↦ QZ.toAddCircle.injective (h'.trans (map_zero _).symm),
      fun h' ↦ (congrArg QZ.toAddCircle h').trans (map_zero _)⟩
  have hN : (E.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup).Normal := by
    rw [hEU]
    exact (charKerOpen χ).isNormal'
  have : IsMulCommutative (E.1 ≃ₐ[K.1] E.1) := ⟨⟨fun τ₁ τ₂ ↦ by
    obtain ⟨g₁, rfl⟩ := restrictHom_surjective (E := E) τ₁
    obtain ⟨g₂, rfl⟩ := restrictHom_surjective (E := E) τ₂
    rw [← map_mul, ← map_mul, ← mul_inv_eq_one, ← map_inv, ← map_mul, ← MonoidHom.mem_ker, FiniteSubfield.ker_restrictHom,
      Subgroup.mem_subgroupOf, hmem]
    simp only [mul_inv_rev, ofMul_mul, ofMul_inv, map_add, map_neg]
    abel⟩⟩
  exact finsum_char_ideleLocalSymbolAt_eq ι E χ (fun h hh ↦ (hmem h).1 hh) x g
    (restrictHom_eq_ideleSymbol_of_artinMap E x g hg)

end

end GroundTheory.Global
