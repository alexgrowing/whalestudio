import Mathlib
import GroundTheory.ProfiniteCohomology.RestrictedRamification.EqZeroOfCohomologyInflThreeEqZero
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BrauerSplit
import GroundTheory.ProfiniteCohomology.GlobalClassFormation
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits NumberField IsDedekindDomain IntermediateField GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1)))

abbrev gsKernel : Subgroup K.1.fixingSubgroup := (gsRestrict K S).ker

theorem isClosed_gsKernel : IsClosed (gsKernel K S : Set K.1.fixingSubgroup) := by
  have ht2 : T2Space (galUnramifiedOutside K.1 ℚ̄ S) :=
    galois_t2Space K.1 (maxUnramifiedOutside K.1 ℚ̄ S)
  have : T1Space (galUnramifiedOutside K.1 ℚ̄ S) := @T2Space.t1Space _ _ ht2
  exact (isClosed_singleton (x := (1 : galUnramifiedOutside K.1 ℚ̄ S))).preimage (continuous_gsRestrict K S)

theorem mem_gsKernel_iff (σ : K.1.fixingSubgroup) :
    σ ∈ gsKernel K S ↔ ∀ x ∈ maxUnramifiedOutside K.1 ℚ̄ S, (σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) x = x := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h x hx
    have := congrArg (fun τ : galUnramifiedOutside K.1 ℚ̄ S =>
      ((τ ⟨x, hx⟩ : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄)) h
    rw [gsRestrict_apply] at this
    exact this
  · intro h
    refine AlgEquiv.ext fun x => Subtype.ext ?_
    rw [gsRestrict_apply]
    exact h x x.2

theorem exists_finiteSubfield_of_isOpen (U : Subgroup K.1.fixingSubgroup)
    (hU : IsOpen (U : Set K.1.fixingSubgroup)) (hNU : gsKernel K S ≤ U) :
    ∃ (L : FiniteSubfield) (_ : Fact (K ≤ L)), (∀ x ∈ L.1, x ∈ maxUnramifiedOutside K.1 ℚ̄ S) ∧
      U = L.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup := by
  have : IsGalois ℚ ℚ̄ := IsAlgClosure.isGalois ℚ ℚ̄
  let U' : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄) := U.map K.1.fixingSubgroup.subtype
  have hKo : IsOpen (K.1.fixingSubgroup : Set (ℚ̄ ≃ₐ[ℚ] ℚ̄)) := K.1.fixingSubgroup_isOpen
  have hU'o : IsOpen (U' : Set (ℚ̄ ≃ₐ[ℚ] ℚ̄)) := by
    have e : (U' : Set (ℚ̄ ≃ₐ[ℚ] ℚ̄)) = Subtype.val '' (U : Set K.1.fixingSubgroup) := by
      ext σ
      simp [U', Subgroup.coe_map]
    rw [e]
    exact hKo.isOpenMap_subtype_val _ hU
  have hU'c : IsClosed (U' : Set (ℚ̄ ≃ₐ[ℚ] ℚ̄)) := Subgroup.isClosed_of_isOpen _ hU'o
  let L' : IntermediateField ℚ ℚ̄ := IntermediateField.fixedField U'
  have hfix : L'.fixingSubgroup = U' := InfiniteGalois.fixingSubgroup_fixedField ⟨U', hU'c⟩
  have hfin : FiniteDimensional ℚ L' := (InfiniteGalois.isOpen_iff_finite L').1 (hfix ▸ hU'o)
  let L : FiniteSubfield := ⟨L', hfin⟩
  have hmemU' : ∀ τ : K.1.fixingSubgroup, (τ : ℚ̄ ≃ₐ[ℚ] ℚ̄) ∈ U' ↔ τ ∈ U := fun τ =>
    Subgroup.mem_map_iff_mem K.1.fixingSubgroup.subtype_injective
  have hKL : K ≤ L := by
    intro x hx
    rw [IntermediateField.mem_fixedField_iff]
    intro σ hσ
    obtain ⟨τ, -, rfl⟩ := Subgroup.mem_map.1 hσ
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 τ.2 x hx
  refine ⟨L, ⟨hKL⟩, fun x hx => ?_, ?_⟩
  · let KS' : IntermediateField ℚ ℚ̄ := (maxUnramifiedOutside K.1 ℚ̄ S).restrictScalars ℚ
    have hx' : x ∈ IntermediateField.fixedField KS'.fixingSubgroup := by
      rw [IntermediateField.mem_fixedField_iff]
      intro σ hσ
      have hσK : σ ∈ K.1.fixingSubgroup := by
        rw [IntermediateField.mem_fixingSubgroup_iff]
        intro y hy
        exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ _
          ((maxUnramifiedOutside K.1 ℚ̄ S).algebraMap_mem (⟨y, hy⟩ : K.1))
      have hσN : (⟨σ, hσK⟩ : K.1.fixingSubgroup) ∈ gsKernel K S :=
        (mem_gsKernel_iff K S _).2 fun y hy =>
          (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ y hy
      have hσU' : σ ∈ U' := (hmemU' ⟨σ, hσK⟩).2 (hNU hσN)
      exact (IntermediateField.mem_fixedField_iff _ _).1 hx σ hσU'
    rw [InfiniteGalois.fixedField_fixingSubgroup KS'] at hx'
    exact hx'
  · ext τ
    rw [Subgroup.mem_subgroupOf, ← hmemU', ← hfix]

theorem isZero_cohomology_one_gsKernel :
    IsZero (cohomology (Rep.res (gsKernel K S).subtype (unitsLimitRep K)) 1) := by
  refine @ModuleCat.isZero_of_subsingleton _ _ _ ⟨fun a b => ?_⟩
  suffices h : ∀ y : cohomology (Rep.res (gsKernel K S).subtype (unitsLimitRep K)) 1, y = 0 by
    rw [h a, h b]
  intro y
  obtain ⟨U, hU, hNU, y', rfl⟩ :=
    exists_isOpen_cohomologyResLE_eq (unitsLimitRep K) (gsKernel K S) (isClosed_gsKernel K S) 1 y
  obtain ⟨L, hL, -, rfl⟩ := exists_finiteSubfield_of_isOpen K S U hU hNU
  have hz : Subsingleton (cohomology (Rep.res (L.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup).subtype
      (unitsLimitRep K)) 1) :=
    ModuleCat.subsingleton_of_isZero (isZero_cohomology_one_res_subgroupOf (K := K) (E := L))
  rw [Subsingleton.elim y' 0, map_zero]

theorem exists_unitsResField_eq_zero_of_pow_nsmul (L : FiniteSubfield) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (x : cohomology (unitsLimitRep L) 2) (k : ℕ) (hx : ℓ ^ k • x = 0) :
    ∃ (E : FiniteSubfield) (_ : Fact (L ≤ E)) (b : ℕ),
      E.1 = L.1 ⊔ Cyclotomic.rootsOfUnityField (ℓ ^ b) ∧ (unitsResField L E 2).hom x = 0 := by
  classical
  have hℓ2 : 2 < ℓ ^ 2 := by nlinarith [hℓ.two_le]
  have : NeZero (ℓ ^ 2) := ⟨pow_ne_zero _ hℓ.ne_zero⟩

  let F₂ : FiniteSubfield := ⟨Cyclotomic.rootsOfUnityField (ℓ ^ 2), inferInstance⟩
  let K' : FiniteSubfield := CyclotomicSymbol.compositum L F₂
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fact (F₂ ≤ K') := CyclotomicSymbol.fact_le_compositum_right L F₂
  have : IsTotallyComplex F₂.1 := IsCyclotomicExtension.Rat.isTotallyComplex (n := ℓ ^ 2) F₂.1 hℓ2
  let _ : Algebra F₂.1 K'.1 := FiniteSubfield.algebraOfLE (Fact.out : F₂ ≤ K')
  have : IsTotallyComplex K'.1 := NumberField.isTotallyComplex_of_algebra (F := F₂.1) K'.1
  obtain ⟨ι'⟩ := nonempty_localEmbeddings K'
  set x' := (unitsResField L K' 2).hom x with hx'
  have hm : (ℓ ^ k) • x' = 0 := by rw [hx', ← map_nsmul, hx, map_zero]

  let T : Finset (HeightOneSpectrum (𝓞 K'.1)) :=
    (brauerLocal ι' x').support.preimage Sum.inr Sum.inr_injective.injOn
  obtain ⟨r, ⟨N, hr⟩, hdeg⟩ :=
    CyclotomicLayer.exists_pow_dvd_finrank_cyclotomicLayer K' T (pow_ne_zero k hℓ.ne_zero)
  let E' : FiniteSubfield := CyclotomicLayer.cyclotomicLayer K' r
  have hsplit : (unitsResField K' E' 2).hom x' = 0 := by
    refine unitsResField_eq_zero_of_dvd_finrank ι' x' (ℓ ^ k) hm (fun v => ?_) fun v hv w => ?_
    · have := subsingleton_cohomology_two_of_isComplex v (IsTotallyComplex.isComplex v)
      exact Subsingleton.elim (α := cohomology (galUnitsZ v.Completion (AlgebraicClosure v.Completion)) 2) _ _
    · exact hdeg v (by rw [Finset.mem_preimage, DFinsupp.mem_support_iff]; exact hv) w

  let a := k * (N + 1)
  let b := a + Cyclotomic.unitsLevel ℓ + 2
  have : NeZero (ℓ ^ b) := ⟨pow_ne_zero _ hℓ.ne_zero⟩
  let F : FiniteSubfield := ⟨Cyclotomic.rootsOfUnityField (ℓ ^ b), inferInstance⟩
  let E : FiniteSubfield := CyclotomicSymbol.compositum L F
  have hrq : r = Cyclotomic.primePowPNat ℓ a := by
    apply PNat.eq
    rw [hr, Cyclotomic.coe_primePowPNat, ← pow_mul]
  have hF₂F : F₂.1 ≤ F.1 := rootsOfUnityField_pow_le (by omega)
  have hZF : (CyclotomicLayer.zhatLayer r).1 ≤ F.1 := by
    rw [hrq, CyclotomicLayer.zhatLayer_coe]
    exact (CyclotomicLayer.zhatLayerField_le_rootsOfUnityField ⟨ℓ, hℓ⟩ a).trans
      (rootsOfUnityField_pow_le (a := a + Cyclotomic.unitsLevel ℓ) (b := b) (by omega))
  have hE'E : E' ≤ E := by
    change (L.1 ⊔ F₂.1) ⊔ (CyclotomicLayer.zhatLayer r).1 ≤ L.1 ⊔ F.1
    exact sup_le (sup_le le_sup_left (hF₂F.trans le_sup_right)) (hZF.trans le_sup_right)
  have : Fact (E' ≤ E) := ⟨hE'E⟩
  have hres : (unitsResField L E 2).hom x = 0 := by
    have hKE' : Fact (L ≤ E') := ⟨(Fact.out : L ≤ K').trans (Fact.out : K' ≤ E')⟩
    have h1 := unitsResField_comp_unitsResField (K := L) (E := E') (M := E) 2
    have h2 := unitsResField_comp_unitsResField (K := L) (E := K') (M := E') 2
    rw [← h1, ConcreteCategory.comp_apply, ← h2, ConcreteCategory.comp_apply]
    change (unitsResField E' E 2).hom ((unitsResField K' E' 2).hom x') = 0
    rw [hsplit, map_zero]
  exact ⟨E, inferInstance, b, rfl, hres⟩

section SubgroupOf

variable {K}

abbrev unitsSubgroupOfMap (L : FiniteSubfield) [Fact (K ≤ L)] (n : ℕ) :
    cohomology (Rep.res (L.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup).subtype (unitsLimitRep K)) n ⟶
      cohomology (unitsLimitRep L) n :=
  cohomologyMapAlong (Subgroup.subgroupOfEquivOfLe
      (IntermediateField.fixingSubgroup_le (Fact.out : K ≤ L))).symm.toMonoidHom
    (continuous_subgroupOfEquivOfLe_symm _) (resSubgroupOfHom _ unitsRep) n

theorem unitsSubgroupOfMap_injective (L : FiniteSubfield) [Fact (K ≤ L)] (n : ℕ) :
    Function.Injective (unitsSubgroupOfMap (K := K) L n).hom :=
  (ModuleCat.mono_iff_injective _).1 inferInstance

theorem fixingSubgroup_subgroupOf_mono {L E : FiniteSubfield} (h : L ≤ E) :
    E.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup ≤ L.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup :=
  fun _ hσ => IntermediateField.fixingSubgroup_le h hσ

theorem cohomologyResLE_comp_unitsSubgroupOfMap {L E : FiniteSubfield} [Fact (K ≤ L)] [Fact (K ≤ E)]
    [Fact (L ≤ E)] (n : ℕ) :
    cohomologyResLE (unitsLimitRep K) (fixingSubgroup_subgroupOf_mono (K := K) (Fact.out : L ≤ E)) n ≫
      unitsSubgroupOfMap E n = unitsSubgroupOfMap L n ≫ unitsResField L E n := by
  rw [cohomologyResLE_eq, ← cohomologyMapAlong_comp, unitsResField, ← cohomologyMapAlong_comp]
  exact cohomologyMapAlong_congr _ _ _ _ (by ext; rfl) (fun _ => rfl) n

end SubgroupOf

theorem exists_coprime_smul_cohomology_two_gsKernel {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (y : cohomology (Rep.res (gsKernel K S).subtype (unitsLimitRep K)) 2) :
    ∃ m : ℕ, m.Coprime ℓ ∧ m • y = 0 := by
  obtain ⟨U, hU, hNU, y', rfl⟩ :=
    exists_isOpen_cohomologyResLE_eq (unitsLimitRep K) (gsKernel K S) (isClosed_gsKernel K S) 2 y
  obtain ⟨L, hL, hLS, rfl⟩ := exists_finiteSubfield_of_isOpen K S U hU hNU
  set yL := (unitsSubgroupOfMap L 2).hom y'
  have htor := isTorsion_cohomology (unitsLimitRep L) (by norm_num : 1 ≤ 2) yL
  set M := addOrderOf yL
  have hM : M ≠ 0 := (IsOfFinAddOrder.addOrderOf_pos htor).ne'
  set a := M.factorization ℓ
  set M' := M / ℓ ^ a
  have hMN : ℓ ^ a * M' = M := Nat.ordProj_mul_ordCompl_eq_self M ℓ
  have hcop : Nat.Coprime M' ℓ := (Nat.coprime_ordCompl hℓ hM).symm
  have hz : ℓ ^ a • (M' • yL) = 0 := by
    rw [smul_smul, hMN]
    exact addOrderOf_nsmul_eq_zero yL
  obtain ⟨E, hE, b, hEb, hres⟩ := exists_unitsResField_eq_zero_of_pow_nsmul L hℓ (M' • yL) a hz
  have hES : ∀ x ∈ E.1, x ∈ maxUnramifiedOutside K.1 ℚ̄ S := by
    have hle : E.1 ≤ (maxUnramifiedOutside K.1 ℚ̄ S).restrictScalars ℚ := by
      rw [hEb]
      refine sup_le (fun x hx => hLS x hx) fun x hx => ?_
      exact mem_maxUnramifiedOutside_of_mem_rootsOfUnityField hℓ hS b x hx
    exact fun x hx => hle hx
  have : Fact (K ≤ E) := ⟨hL.out.trans hE.out⟩
  have hNE : gsKernel K S ≤ E.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup := fun σ hσ =>
    (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx =>
      (mem_gsKernel_iff K S σ).1 hσ x (hES x hx)
  have hEL := fixingSubgroup_subgroupOf_mono (K := K) hE.out

  have hr : (cohomologyResLE (unitsLimitRep K) hEL 2).hom (M' • y') = 0 := by
    apply unitsSubgroupOfMap_injective E 2
    have e := congrArg (fun φ => ModuleCat.Hom.hom φ (M' • y'))
      (cohomologyResLE_comp_unitsSubgroupOfMap (K := K) (L := L) (E := E) 2)
    refine e.trans ?_
    change (unitsResField L E 2).hom ((unitsSubgroupOfMap L 2).hom (M' • y')) = _
    rw [map_nsmul, hres, map_zero]
  refine ⟨M', hcop, ?_⟩
  rw [← map_nsmul, ← cohomologyResLE_comp (unitsLimitRep K) hEL hNE 2, ConcreteCategory.comp_apply, hr,
    map_zero]

end

end GroundTheory.ProfCoh
