import Mathlib
import GroundTheory.LocalFields.AbstractLocalReciprocity.ExistsOpenSubgroupMemFixedModule

namespace GroundTheory.LocalField.Abstract

variable {G : Type*} [Group G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]

section Self

variable (K : Subgroup G)

instance uniqueQuotientSubgroupOfSelf : Unique (K ⧸ K.subgroupOf K) where
  default := ((1 : K) : K ⧸ K.subgroupOf K)
  uniq q := by
    induction q using QuotientGroup.induction_on with
    | H σ =>
      rw [QuotientGroup.eq]
      simp

instance finiteIndex_subgroupOf_self : (K.subgroupOf K).FiniteIndex :=
  ⟨by simp [Subgroup.subgroupOf_self]⟩

theorem norm_self : norm A K K = MonoidHom.id (fixedModule A K) := by
  refine MonoidHom.ext fun a => Subtype.ext ?_
  rw [coe_norm, finprod_unique]
  show ((1 : K) : G) • (a : A) = a
  simp

end Self

section Pow

variable {K L : Subgroup G} [(L.subgroupOf K).FiniteIndex]

theorem coe_norm_of_mem (hLK : L ≤ K) {a : A} (ha : a ∈ fixedModule A K) :
    (norm A K L ⟨a, fixedModule_anti hLK ha⟩ : A) = a ^ L.relIndex K := by
  classical
  let _ := Fintype.ofFinite (K ⧸ L.subgroupOf K)
  rw [coe_norm, finprod_eq_prod_of_fintype]
  have h : ∀ q : K ⧸ L.subgroupOf K, cosetSMul A K L ⟨a, fixedModule_anti hLK ha⟩ q = a := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H σ => exact ha σ σ.2
  simp_rw [h]
  rw [Finset.prod_const, Finset.card_univ, ← Nat.card_eq_fintype_card, Subgroup.relIndex,
    Subgroup.index_eq_card]

end Pow

section Transitivity

variable {K L M : Subgroup G}

def cosetShift (hLK : L ≤ K) (σ : K) : L ⧸ M.subgroupOf L → K ⧸ M.subgroupOf K :=
  Quotient.map' (fun τ : L => σ * (⟨τ, hLK τ.2⟩ : K)) fun τ τ' h => by
    rw [QuotientGroup.leftRel_apply] at h ⊢
    simpa [Subgroup.mem_subgroupOf, mul_assoc] using h

@[simp] theorem cosetShift_mk (hLK : L ≤ K) (σ : K) (τ : L) :
    cosetShift (M := M) hLK σ (τ : L ⧸ M.subgroupOf L) =
      ((σ * (⟨τ, hLK τ.2⟩ : K) : K) : K ⧸ M.subgroupOf K) :=
  rfl

theorem norm_norm (hML : M ≤ L) (hLK : L ≤ K) [(L.subgroupOf K).FiniteIndex]
    [(M.subgroupOf L).FiniteIndex] [(M.subgroupOf K).FiniteIndex] (a : fixedModule A M) :
    norm A K L (norm A L M a) = norm A K M a := by
  classical
  let _ := Fintype.ofFinite (K ⧸ M.subgroupOf K)
  let _ := Fintype.ofFinite (K ⧸ L.subgroupOf K)
  let _ := Fintype.ofFinite (L ⧸ M.subgroupOf L)
  have hle : M.subgroupOf K ≤ L.subgroupOf K := fun x hx => hML hx
  ext
  simp only [coe_norm, finprod_eq_prod_of_fintype]
  rw [← Finset.prod_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ)
    (g := Subgroup.quotientMapOfLE hle) (fun _ _ => Finset.mem_univ _)]
  refine Finset.prod_congr rfl fun p _ => ?_
  induction p using QuotientGroup.induction_on with
  | H σ =>
    rw [cosetSMul_mk, coe_norm, finprod_eq_prod_of_fintype, Finset.smul_prod']
    refine Finset.prod_bij (fun t _ => cosetShift hLK σ t) ?_ ?_ ?_ ?_
    · intro t _
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      induction t using QuotientGroup.induction_on with
      | H τ =>
        rw [cosetShift_mk, Subgroup.quotientMapOfLE_apply_mk, QuotientGroup.eq]
        simp [Subgroup.mem_subgroupOf, mul_assoc]
    · intro t _ t' _ h
      induction t using QuotientGroup.induction_on with
      | H τ =>
      induction t' using QuotientGroup.induction_on with
      | H τ' =>
        rw [cosetShift_mk, cosetShift_mk, QuotientGroup.eq] at h
        rw [QuotientGroup.eq]
        simpa [Subgroup.mem_subgroupOf, mul_assoc] using h
    · intro q hq
      rw [Finset.mem_filter] at hq
      induction q using QuotientGroup.induction_on with
      | H ρ =>
        have h := hq.2
        rw [Subgroup.quotientMapOfLE_apply_mk, QuotientGroup.eq] at h
        have hmem : (σ : G)⁻¹ * ρ ∈ L := by
          have := L.inv_mem h
          simpa [Subgroup.mem_subgroupOf, mul_inv_rev] using this
        refine ⟨((⟨(σ : G)⁻¹ * ρ, hmem⟩ : L) : L ⧸ M.subgroupOf L), Finset.mem_univ _, ?_⟩
        rw [cosetShift_mk]
        congr 1
        ext
        simp
    · intro t _
      induction t using QuotientGroup.induction_on with
      | H τ =>
        rw [cosetShift_mk, cosetSMul_mk, cosetSMul_mk, smul_smul]
        rfl

theorem range_norm_le_range_norm (hML : M ≤ L) (hLK : L ≤ K) [(L.subgroupOf K).FiniteIndex]
    [(M.subgroupOf L).FiniteIndex] [(M.subgroupOf K).FiniteIndex] :
    (norm A K M).range ≤ (norm A K L).range := by
  rintro _ ⟨a, rfl⟩
  exact ⟨norm A L M a, norm_norm hML hLK a⟩

end Transitivity

section Conjugation

variable {K L : Subgroup G}

def cosetConj (σ : G) :
    K ⧸ L.subgroupOf K →
      K.map (MulAut.conj σ).toMonoidHom ⧸
        (L.map (MulAut.conj σ).toMonoidHom).subgroupOf (K.map (MulAut.conj σ).toMonoidHom) :=
  Quotient.map' (fun τ : K => (⟨σ * τ * σ⁻¹, τ, τ.2, rfl⟩ : K.map (MulAut.conj σ).toMonoidHom))
    fun τ τ' h => by
      rw [QuotientGroup.leftRel_apply] at h ⊢
      rw [Subgroup.mem_subgroupOf] at h ⊢
      refine ⟨(τ : G)⁻¹ * τ', by simpa using h, ?_⟩
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

@[simp] theorem cosetConj_mk (σ : G) (τ : K) :
    cosetConj (L := L) σ (τ : K ⧸ L.subgroupOf K) =
      ((⟨σ * τ * σ⁻¹, τ, τ.2, rfl⟩ : K.map (MulAut.conj σ).toMonoidHom) : _ ⧸ _) :=
  rfl

theorem smul_norm (σ : G) [(L.subgroupOf K).FiniteIndex]
    [((L.map (MulAut.conj σ).toMonoidHom).subgroupOf (K.map (MulAut.conj σ).toMonoidHom)).FiniteIndex]
    (a : fixedModule A L) :
    σ • (norm A K L a : A) =
      norm A (K.map (MulAut.conj σ).toMonoidHom) (L.map (MulAut.conj σ).toMonoidHom)
        ⟨σ • (a : A), smul_mem_fixedModule a.2 σ⟩ := by
  classical
  let _ := Fintype.ofFinite (K ⧸ L.subgroupOf K)
  let _ := Fintype.ofFinite (K.map (MulAut.conj σ).toMonoidHom ⧸
    (L.map (MulAut.conj σ).toMonoidHom).subgroupOf (K.map (MulAut.conj σ).toMonoidHom))
  rw [coe_norm, coe_norm, finprod_eq_prod_of_fintype, finprod_eq_prod_of_fintype, Finset.smul_prod']
  refine Finset.prod_bij (fun t _ => cosetConj σ t) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro t _ t' _ h
    induction t using QuotientGroup.induction_on with
    | H τ =>
    induction t' using QuotientGroup.induction_on with
    | H τ' =>
      rw [cosetConj_mk, cosetConj_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      obtain ⟨x, hx, hx'⟩ := h
      have : x = (τ : G)⁻¹ * τ' := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul,
          InvMemClass.coe_inv, mul_inv_rev, inv_inv] at hx'
        have := congrArg (fun y => σ⁻¹ * y * σ) hx'
        simpa [mul_assoc] using this
      simpa [this] using hx
  · intro q _
    induction q using QuotientGroup.induction_on with
    | H ρ =>
      obtain ⟨κ, hκ, hκρ⟩ := Subgroup.mem_map.1 ρ.2
      refine ⟨((⟨κ, hκ⟩ : K) : K ⧸ L.subgroupOf K), Finset.mem_univ _, ?_⟩
      rw [cosetConj_mk]
      congr 1
      ext
      simpa using hκρ
  · intro t _
    induction t using QuotientGroup.induction_on with
    | H τ =>
      rw [cosetConj_mk, cosetSMul_mk, cosetSMul_mk, smul_smul, smul_smul]
      simp

end Conjugation

end GroundTheory.LocalField.Abstract
