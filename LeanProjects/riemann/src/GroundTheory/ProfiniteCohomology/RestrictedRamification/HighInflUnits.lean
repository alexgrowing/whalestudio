import Mathlib
import GroundTheory.ProfiniteCohomology.RestrictedRamification.HighInfl
import GroundTheory.ProfiniteCohomology.RestrictedRamification.CohomologyMapAlongInvariantsGsKernelMorCompGsBra
import GroundTheory.ProfiniteCohomology.RestrictedRamification.Brauer
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.HighUnits
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits NumberField IsDedekindDomain IntermediateField GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

section Primary

variable {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] {ℓ : ℕ} {f : X →+ Y}

theorem IsIsoModCoprime.eq_zero_of_pow_nsmul (h : IsIsoModCoprime ℓ f) {x : X} (hx : f x = 0) {k : ℕ}
    (hk : ℓ ^ k • x = 0) : x = 0 := by
  obtain ⟨m, hm, hmx⟩ := h.1 x hx
  exact eq_zero_of_coprime_nsmul_eq_zero hm hmx hk

theorem IsIsoModCoprime.exists_pow_nsmul (h : IsIsoModCoprime ℓ f) (hℓ : ℓ.Prime) (hX : IsAddTorsion X)
    {y : Y} {k : ℕ} (hk : ℓ ^ k • y = 0) : ∃ x, (∃ j : ℕ, ℓ ^ j • x = 0) ∧ f x = y := by
  obtain ⟨m, hm, x, hx⟩ := h.2 y
  obtain ⟨u, w, huw⟩ : IsCoprime (m : ℤ) ((ℓ ^ k : ℕ) : ℤ) := Nat.isCoprime_iff_coprime.2 (hm.pow_right k)
  have hy : f (u • x) = y := by
    rw [map_zsmul, hx]
    calc u • (m • y) = (u * m) • y := by rw [mul_smul, natCast_zsmul]
      _ = (u * m + w * ((ℓ ^ k : ℕ) : ℤ)) • y := by
        rw [add_smul, mul_smul w, natCast_zsmul, hk, smul_zero, add_zero]
      _ = y := by rw [huw, one_smul]
  obtain ⟨x', hx', hfx'⟩ := exists_primary_map_eq f hℓ (hX (u • x)) (k := k) (by rw [hy]; exact hk)
  exact ⟨x', hx', hfx'.trans hy⟩

def primaryComponentMap (ℓ : ℕ) (f : X →+ Y) :
    AddCommGroup.primaryComponent X ℓ →+ AddCommGroup.primaryComponent Y ℓ :=
  (f.comp (AddCommGroup.primaryComponent X ℓ).subtype).codRestrict _ fun x => by
    obtain ⟨k, hk⟩ := x.2
    exact ⟨k, (map_nsmul f _ _).symm.trans ((congrArg f hk).trans (map_zero f))⟩

theorem coe_primaryComponentMap_apply (x : AddCommGroup.primaryComponent X ℓ) :
    (primaryComponentMap ℓ f x : Y) = f x :=
  rfl

theorem IsIsoModCoprime.bijective_primaryComponentMap (h : IsIsoModCoprime ℓ f) (hℓ : ℓ.Prime)
    (hX : IsAddTorsion X) : Function.Bijective (primaryComponentMap ℓ f) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, fun y => ?_⟩
  · obtain ⟨k, hk⟩ := x.2
    exact Subtype.ext (h.eq_zero_of_pow_nsmul (congrArg Subtype.val hx) hk)
  · obtain ⟨k, hk⟩ := y.2
    obtain ⟨x, ⟨j, hj⟩, hx⟩ := h.exists_pow_nsmul hℓ hX hk
    exact ⟨⟨x, j, hj⟩, Subtype.ext hx⟩

end Primary

variable (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1)))

section Kernel

variable {ℓ : ℕ} (hℓ : ℓ.Prime) (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)

include hℓ hS in

theorem eq_zero_cohomology_gsKernel_of_three_le {r : ℕ} (hr : 3 ≤ r)
    (y : cohomology (Rep.res (gsKernel K S).subtype (unitsLimitRep K)) r) : y = 0 := by
  obtain ⟨U, hU, hNU, y', rfl⟩ :=
    exists_isOpen_cohomologyResLE_eq (unitsLimitRep K) (gsKernel K S) (isClosed_gsKernel K S) r y
  obtain ⟨L, hL, hLS, rfl⟩ := exists_finiteSubfield_of_isOpen K S U hU hNU
  have hℓ2 : 2 < ℓ ^ 2 := by nlinarith [hℓ.two_le]
  have : NeZero (ℓ ^ 2) := ⟨pow_ne_zero _ hℓ.ne_zero⟩
  let F₂ : FiniteSubfield := ⟨Cyclotomic.rootsOfUnityField (ℓ ^ 2), inferInstance⟩
  let E : FiniteSubfield := CyclotomicSymbol.compositum L F₂
  have : Fact (F₂ ≤ E) := CyclotomicSymbol.fact_le_compositum_right L F₂
  have : IsTotallyComplex F₂.1 := IsCyclotomicExtension.Rat.isTotallyComplex (n := ℓ ^ 2) F₂.1 hℓ2
  let _ : Algebra F₂.1 E.1 := FiniteSubfield.algebraOfLE (Fact.out : F₂ ≤ E)
  have : IsTotallyComplex E.1 := NumberField.isTotallyComplex_of_algebra (F := F₂.1) E.1
  have hLE : Fact (L ≤ E) := CyclotomicSymbol.fact_le_compositum_left L F₂
  have : Fact (K ≤ E) := ⟨hL.out.trans hLE.out⟩
  have hES : ∀ x ∈ E.1, x ∈ maxUnramifiedOutside K.1 ℚ̄ S := by
    have hle : E.1 ≤ (maxUnramifiedOutside K.1 ℚ̄ S).restrictScalars ℚ := by
      change L.1 ⊔ F₂.1 ≤ _
      refine sup_le (fun x hx => hLS x hx) fun x hx => ?_
      exact mem_maxUnramifiedOutside_of_mem_rootsOfUnityField hℓ hS 2 x hx
    exact fun x hx => hle hx
  have hNE : gsKernel K S ≤ E.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup := fun σ hσ =>
    (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx =>
      (mem_gsKernel_iff K S σ).1 hσ x (hES x hx)
  have hEL := fixingSubgroup_subgroupOf_mono (K := K) hLE.out
  have hz : (cohomologyResLE (unitsLimitRep K) hEL r).hom y' = 0 := by
    apply unitsSubgroupOfMap_injective E r
    have : Subsingleton (cohomology (unitsLimitRep E) r) :=
      subsingleton_cohomology_unitsLimitRep_of_three_le (fun v => IsTotallyComplex.isComplex v) hr
    exact Subsingleton.elim _ _
  rw [← cohomologyResLE_comp (unitsLimitRep K) hEL hNE r, ConcreteCategory.comp_apply, hz, map_zero]

include hℓ hS in

theorem exists_coprime_nsmul_cohomology_gsKernel {i : ℕ} (hi : 1 ≤ i)
    (y : cohomology (Rep.res (gsKernel K S).subtype (unitsLimitRep K)) i) :
    ∃ m : ℕ, m.Coprime ℓ ∧ m • y = 0 := by
  rcases (show i = 1 ∨ i = 2 ∨ 3 ≤ i by omega) with rfl | rfl | h3
  · have := ModuleCat.subsingleton_of_isZero (isZero_cohomology_one_gsKernel K S)
    exact ⟨1, Nat.coprime_one_left ℓ, Subsingleton.elim _ _⟩
  · exact exists_coprime_smul_cohomology_two_gsKernel K S hℓ hS y
  · exact ⟨1, Nat.coprime_one_left ℓ, by rw [eq_zero_cohomology_gsKernel_of_three_le K S hℓ hS h3 y, smul_zero]⟩

end Kernel

def gsUnitsInfl (r : ℕ) :
    cohomology (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) r →+ cohomology (unitsLimitRep K) r :=
  (gsBrauerInfl K S r).hom.toAddMonoidHom.comp
    (cohomologyULiftIntAddEquiv (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) r).toAddMonoidHom

theorem gsUnitsInfl_apply (r : ℕ) (x : cohomology (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) r) :
    gsUnitsInfl K S r x =
      (gsBrauerInfl K S r).hom (cohomologyULiftIntAddEquiv (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) r x) :=
  rfl

variable {ℓ : ℕ} (hℓ : ℓ.Prime) (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)

include hℓ hS in

theorem isIsoModCoprime_gsUnitsInfl {r : ℕ} (hr : 1 ≤ r) : IsIsoModCoprime ℓ (gsUnitsInfl K S r) := by
  have h := isIsoModCoprime_cohomologyInfl (isClosed_gsKernel K S) ℓ hr
    (fun i hi y => exists_coprime_nsmul_cohomology_gsKernel K S hℓ hS hi y)
  have hsurj : Function.Surjective (cohomologyMapAlong (gsQuotientEquiv K S).toMonoidHom
      (continuous_gsQuotientEquiv K S) (invariantsGsKernelMor K S) r).hom :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  have hinj : Function.Injective (cohomologyMapAlong (gsQuotientEquiv K S).toMonoidHom
      (continuous_gsQuotientEquiv K S) (invariantsGsKernelMor K S) r).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  have he : ∀ x, (cohomologyInfl (unitsLimitRep K) (gsKernel K S) r).hom x =
      (gsBrauerInfl K S r).hom ((cohomologyMapAlong (gsQuotientEquiv K S).toMonoidHom
        (continuous_gsQuotientEquiv K S) (invariantsGsKernelMor K S) r).hom x) := fun x =>
    (congrArg (fun φ => φ.hom x) (cohomologyMapAlong_invariantsGsKernelMor_comp_gsBrauerInfl K S r)).symm
  have h' : IsIsoModCoprime ℓ (gsBrauerInfl K S r).hom.toAddMonoidHom :=
    IsIsoModCoprime.of_comp_surjective (e := (cohomologyMapAlong (gsQuotientEquiv K S).toMonoidHom
      (continuous_gsQuotientEquiv K S) (invariantsGsKernelMor K S) r).hom.toAddMonoidHom) (h.congr he) hsurj
  exact h'.comp (IsIsoModCoprime.of_bijective
    (cohomologyULiftIntAddEquiv (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) r).bijective)

include hℓ hS in

theorem eq_zero_of_gsUnitsInfl_eq_zero {r : ℕ} (hr : 1 ≤ r)
    (x : cohomology (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) r) (hx : gsUnitsInfl K S r x = 0) {k : ℕ}
    (hk : ℓ ^ k • x = 0) : x = 0 :=
  (isIsoModCoprime_gsUnitsInfl K S hℓ hS hr).eq_zero_of_pow_nsmul hx hk

include hℓ hS in

theorem exists_gsUnitsInfl_eq {r : ℕ} (hr : 1 ≤ r) (y : cohomology (unitsLimitRep K) r) {k : ℕ}
    (hk : ℓ ^ k • y = 0) : ∃ x, (∃ j : ℕ, ℓ ^ j • x = 0) ∧ gsUnitsInfl K S r x = y :=
  (isIsoModCoprime_gsUnitsInfl K S hℓ hS hr).exists_pow_nsmul hℓ (isTorsion_cohomology _ hr) hk

noncomputable def gsUnitsInflPrimaryEquiv {r : ℕ} (hr : 1 ≤ r) :
    AddCommGroup.primaryComponent (cohomology (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) r) ℓ ≃+
      AddCommGroup.primaryComponent (cohomology (unitsLimitRep K) r) ℓ :=
  AddEquiv.ofBijective (primaryComponentMap ℓ (gsUnitsInfl K S r))
    ((isIsoModCoprime_gsUnitsInfl K S hℓ hS hr).bijective_primaryComponentMap hℓ (isTorsion_cohomology _ hr))

theorem coe_gsUnitsInflPrimaryEquiv_apply {r : ℕ} (hr : 1 ≤ r)
    (x : AddCommGroup.primaryComponent (cohomology (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) r) ℓ) :
    (gsUnitsInflPrimaryEquiv K S hℓ hS hr x : cohomology (unitsLimitRep K) r) = gsUnitsInfl K S r x :=
  rfl

end

end GroundTheory.ProfCoh
