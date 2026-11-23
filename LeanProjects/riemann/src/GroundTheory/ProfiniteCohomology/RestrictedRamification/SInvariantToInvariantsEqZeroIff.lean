import Mathlib
import GroundTheory.ProfiniteCohomology.RestrictedRamification.SDivisor
import GroundTheory.ProfiniteCohomology.GaloisCohomology.Kummer
import GroundTheory.ProfiniteCohomology.GaloisCohomology.IsZeroGroupCohomologyQuotientToInvariantsGalAdd
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum CategoryTheory

universe u

section Quot

variable (F Ω : Type u) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
variable (S : Set (HeightOneSpectrum (𝓞 F)))

def sUnitsSubmodule : Submodule (ULift.{u} ℤ) (galUnits.{u} F (maxUnramifiedOutside F Ω S)) where
  carrier := {z | Additive.toMul (α := (maxUnramifiedOutside F Ω S)ˣ) z ∈ sUnitsMax F Ω S}
  add_mem' {a b} ha hb := by
    change Additive.toMul (α := (maxUnramifiedOutside F Ω S)ˣ) a *
      Additive.toMul (α := (maxUnramifiedOutside F Ω S)ˣ) b ∈ sUnitsMax F Ω S
    exact mul_mem ha hb
  zero_mem' := by
    change (1 : (maxUnramifiedOutside F Ω S)ˣ) ∈ sUnitsMax F Ω S
    exact one_mem _
  smul_mem' r z hz := by
    change Additive.toMul (α := (maxUnramifiedOutside F Ω S)ˣ) (r.down • z) ∈ sUnitsMax F Ω S
    rw [toMul_zsmul]
    exact zpow_mem hz _

theorem sUnitsSubmodule_le_comap (σ : galUnramifiedOutside F Ω S) :
    sUnitsSubmodule F Ω S ≤ (sUnitsSubmodule F Ω S).comap
      ((galUnits.{u} F (maxUnramifiedOutside F Ω S)).ρ σ) :=
  fun _ hz => galUnitsHom_mem_sUnitsOf (S := S) σ hz

noncomputable abbrev galUnitsModSUnits : Rep.{u} (ULift.{u} ℤ) (galUnramifiedOutside F Ω S) :=
  (galUnits.{u} F (maxUnramifiedOutside F Ω S)).quotient (sUnitsSubmodule F Ω S)
    (sUnitsSubmodule_le_comap F Ω S)

noncomputable def sUnitsQuotSequence :
    ShortComplex (Rep.{u} (ULift.{u} ℤ) (galUnramifiedOutside F Ω S)) :=
  ShortComplex.mk (sUnitsToUnits S (maxUnramifiedOutside F Ω S))
    (Rep.mkQ _ (sUnitsSubmodule F Ω S) (sUnitsSubmodule_le_comap F Ω S)) (by
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro x
      exact (Submodule.Quotient.mk_eq_zero _).2
        (show Additive.toMul (α := (maxUnramifiedOutside F Ω S)ˣ) _ ∈ sUnitsMax F Ω S from
          (Additive.toMul x).2))

theorem sUnitsQuotSequence_shortExact : (sUnitsQuotSequence F Ω S).ShortExact where
  exact := by
    apply shortComplex_exact_of_forall_exists
    intro x hx
    exact ⟨Additive.ofMul ⟨Additive.toMul (α := (maxUnramifiedOutside F Ω S)ˣ) x,
      (Submodule.Quotient.mk_eq_zero _).1 hx⟩, rfl⟩
  mono_f := (Rep.mono_iff_injective _).2 (sUnitsToUnits_injective S _)
  epi_g := (Rep.epi_iff_surjective _).2 (Submodule.mkQ_surjective _)

variable [IsGalois F Ω]

instance isDiscreteRep_sUnitsQuotSequence_X₁ : IsDiscreteRep (sUnitsQuotSequence F Ω S).X₁ :=
  inferInstanceAs (IsDiscreteRep (galSUnits S (maxUnramifiedOutside F Ω S)))

instance isDiscreteRep_sUnitsQuotSequence_X₂ : IsDiscreteRep (sUnitsQuotSequence F Ω S).X₂ :=
  inferInstanceAs (IsDiscreteRep (galUnits.{u} F (maxUnramifiedOutside F Ω S)))

instance isDiscreteRep_sUnitsQuotSequence_X₃ : IsDiscreteRep (sUnitsQuotSequence F Ω S).X₃ :=
  isDiscreteRep_quotient _ _ _

end Quot

section Phi

variable {F Ω : Type u} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]
variable (S : Set (HeightOneSpectrum (𝓞 F)))

omit [IsGalois F Ω] in

theorem mk_mem_invariants_iff (x : (maxUnramifiedOutside F Ω S)ˣ) :
    (Rep.mkQ _ (sUnitsSubmodule F Ω S) (sUnitsSubmodule_le_comap F Ω S)).hom
        (Additive.ofMul x : Additive (maxUnramifiedOutside F Ω S)ˣ) ∈
      (galUnitsModSUnits F Ω S).ρ.invariants ↔ IsSInvariant S x :=
  forall_congr' fun _ => (Submodule.Quotient.eq _).trans Iff.rfl

noncomputable def sInvariantToInvariants :
    Additive (sInvariantSubgroup Ω S) →+ (galUnitsModSUnits F Ω S).ρ.invariants where
  toFun x := ⟨(Rep.mkQ _ (sUnitsSubmodule F Ω S) (sUnitsSubmodule_le_comap F Ω S)).hom
      (Additive.ofMul (Additive.toMul x : sInvariantSubgroup Ω S).1 :
        Additive (maxUnramifiedOutside F Ω S)ˣ),
    (mk_mem_invariants_iff S _).2 (Additive.toMul x).2⟩
  map_zero' := rfl
  map_add' _ _ := rfl

omit [IsGalois F Ω] in
theorem sInvariantToInvariants_surjective : Function.Surjective (sInvariantToInvariants (Ω := Ω) S) := by
  rintro ⟨q, hq⟩
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  exact ⟨Additive.ofMul ⟨Additive.toMul (α := (maxUnramifiedOutside F Ω S)ˣ) z,
    (mk_mem_invariants_iff S _).1 hq⟩, rfl⟩

omit [IsGalois F Ω] in
theorem sInvariantToInvariants_eq_zero_iff (x : Additive (sInvariantSubgroup Ω S)) :
    sInvariantToInvariants S x = 0 ↔
      ((Additive.toMul x : sInvariantSubgroup Ω S) : (maxUnramifiedOutside F Ω S)ˣ) ∈ sUnitsMax F Ω S := by
  rw [Subtype.ext_iff]
  exact Submodule.Quotient.mk_eq_zero _

theorem divAbove_eq_zero_of_mem {x : sInvariantSubgroup Ω S}
    (hx : (x : (maxUnramifiedOutside F Ω S)ˣ) ∈ sUnitsMax F Ω S) :
    divAbove S (Additive.ofMul x) = 0 := by
  ext v
  rw [divAbove_apply, Finsupp.coe_zero, Pi.zero_apply]
  obtain ⟨L, hf, hL, y, hy, hyx⟩ := exists_of_mem_sUnitsMax F Ω S hx
  have := NumberField.of_module_finite F L
  have hyL : (((x : (maxUnramifiedOutside F Ω S)ˣ) : maxUnramifiedOutside F Ω S) : Ω) ∈ L := by
    rw [← hyx]
    exact (y : L).2
  obtain ⟨w, hw⟩ := exists_underPlace_eq (L := L) v.1
  have h1 := valuation_eq_exp_ordAbove S x.2 hL hyL w (hw ▸ v.2)
  have hyy : (⟨_, hyL⟩ : L) = (y : L) :=
    Subtype.ext (congrArg (fun u : (maxUnramifiedOutside F Ω S)ˣ =>
      ((u : maxUnramifiedOutside F Ω S) : Ω)) hyx).symm
  have h2 := (mem_sUnitsOf_iff_mem_unit S).1 hy w (fun h => (hw ▸ v.2) (mem_placesOver_iff.1 h))
  rw [hyy, h2, hw] at h1
  have := congrArg WithZero.log h1
  simp only [WithZero.log_one, WithZero.log_exp] at this
  simp only [toMul_ofMul]
  omega

noncomputable def invariantsToSPic : (galUnitsModSUnits F Ω S).ρ.invariants →+ sPic S :=
  (QuotientAddGroup.lift (sInvariantToInvariants (Ω := Ω) S).ker ((sPicMk S).comp (divAbove S))
    (fun x hx => by
      rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply]
      have := divAbove_eq_zero_of_mem S
        ((sInvariantToInvariants_eq_zero_iff S x).1 (AddMonoidHom.mem_ker.1 hx))
      rw [ofMul_toMul] at this
      rw [this, map_zero])).comp
    (QuotientAddGroup.quotientKerEquivOfSurjective _
      (sInvariantToInvariants_surjective (Ω := Ω) S)).symm.toAddMonoidHom

theorem invariantsToSPic_apply (x : Additive (sInvariantSubgroup Ω S)) :
    invariantsToSPic S (sInvariantToInvariants S x) = sPicMk S (divAbove S x) := by
  have h : (QuotientAddGroup.quotientKerEquivOfSurjective _
      (sInvariantToInvariants_surjective (Ω := Ω) S)).symm (sInvariantToInvariants S x) =
      (x : Additive (sInvariantSubgroup Ω S) ⧸ (sInvariantToInvariants (Ω := Ω) S).ker) :=
    (AddEquiv.symm_apply_eq _).2 rfl
  simp only [invariantsToSPic, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, h]
  rfl

noncomputable def invariantsToH1 :
    (galUnitsModSUnits F Ω S).ρ.invariants →+ cohomology (galSUnits S (maxUnramifiedOutside F Ω S)) 1 :=
  (δ (sUnitsQuotSequence_shortExact F Ω S) 0 1 rfl).hom.toAddMonoidHom.comp
    (H0Iso (sUnitsQuotSequence F Ω S).X₃).inv.hom.toAddMonoidHom

theorem invariantsToH1_surjective : Function.Surjective (invariantsToH1 (Ω := Ω) S) := fun x =>
  exists_δ_H0Iso_inv_eq (sUnitsQuotSequence_shortExact F Ω S)
    (subsingleton_cohomology_one_galUnits (K := F) (L := maxUnramifiedOutside F Ω S)) x

theorem invariantsToH1_eq_zero_iff (q : (galUnitsModSUnits F Ω S).ρ.invariants) :
    invariantsToH1 S q = 0 ↔ ∃ a : Fˣ,
      sInvariantToInvariants S (Additive.ofMul ⟨_, map_algebraMap_mem_sInvariantSubgroup (Ω := Ω) S a⟩) = q := by
  refine (δ_H0Iso_inv_eq_zero_iff (sUnitsQuotSequence_shortExact F Ω S) q).trans ?_
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨a, rfl⟩ := unitsToInvariants_surjective F (maxUnramifiedOutside F Ω S) w
    exact ⟨Additive.toMul a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨unitsToInvariants F (maxUnramifiedOutside F Ω S) (Additive.ofMul a), rfl⟩

end Phi

section H1

variable {F Ω : Type u} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]
variable (S : Set (HeightOneSpectrum (𝓞 F)))

noncomputable def h1SUnitsToSPic :
    cohomology (galSUnits S (maxUnramifiedOutside F Ω S)) 1 →+ sPic S :=
  (QuotientAddGroup.lift (invariantsToH1 (Ω := Ω) S).ker (invariantsToSPic S) (fun q hq => by
      obtain ⟨a, rfl⟩ := (invariantsToH1_eq_zero_iff S q).1 (AddMonoidHom.mem_ker.1 hq)
      rw [AddMonoidHom.mem_ker, invariantsToSPic_apply, divAbove_algebraMap]
      exact (sPicMk_eq_zero_iff S _).2 ⟨a, rfl⟩)).comp
    (QuotientAddGroup.quotientKerEquivOfSurjective _
      (invariantsToH1_surjective (Ω := Ω) S)).symm.toAddMonoidHom

theorem h1SUnitsToSPic_invariantsToH1 (q : (galUnitsModSUnits F Ω S).ρ.invariants) :
    h1SUnitsToSPic S (invariantsToH1 S q) = invariantsToSPic S q := by
  have h : (QuotientAddGroup.quotientKerEquivOfSurjective _
      (invariantsToH1_surjective (Ω := Ω) S)).symm (invariantsToH1 S q) =
      (q : (galUnitsModSUnits F Ω S).ρ.invariants ⧸ (invariantsToH1 (Ω := Ω) S).ker) :=
    (AddEquiv.symm_apply_eq _).2 rfl
  simp only [h1SUnitsToSPic, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, h]
  rfl

theorem h1SUnitsToSPic_apply (x : Additive (sInvariantSubgroup Ω S)) :
    h1SUnitsToSPic S (invariantsToH1 S (sInvariantToInvariants S x)) = sPicMk S (divAbove S x) := by
  rw [h1SUnitsToSPic_invariantsToH1, invariantsToSPic_apply]

theorem h1SUnitsToSPic_injective : Function.Injective (h1SUnitsToSPic (Ω := Ω) S) := by
  refine (injective_iff_map_eq_zero _).2 fun h hh => ?_
  obtain ⟨q, rfl⟩ := invariantsToH1_surjective (Ω := Ω) S h
  obtain ⟨x, rfl⟩ := sInvariantToInvariants_surjective (Ω := Ω) S q
  rw [h1SUnitsToSPic_apply, sPicMk_eq_zero_iff] at hh
  obtain ⟨a, ha⟩ := hh
  let y : Additive (sInvariantSubgroup Ω S) :=
    Additive.ofMul ⟨_, map_algebraMap_mem_sInvariantSubgroup (Ω := Ω) S a⟩
  have hxy : divAbove S (x - y) = 0 := by
    rw [map_sub, divAbove_algebraMap, ha, sub_self]
  have hmem := mem_sUnitsMax_of_divAbove_eq_zero S (x := Additive.toMul (x - y)) hxy
  have h0 : sInvariantToInvariants S (x - y) = 0 := (sInvariantToInvariants_eq_zero_iff S _).2 hmem
  rw [map_sub, sub_eq_zero] at h0
  rw [h0]
  exact (invariantsToH1_eq_zero_iff S _).2 ⟨a, rfl⟩

variable [IsSepClosed Ω]

theorem exists_h1SUnitsToSPic_eq {N : ℕ} (hN : N ≠ 0)
    (hNS : ∀ v ∉ S, ((N : ℕ) : 𝓞 F) ∉ v.asIdeal) (c : sPic S) (hc : N • c = 0) :
    ∃ h, h1SUnitsToSPic (Ω := Ω) S h = c := by
  obtain ⟨D, rfl⟩ := QuotientAddGroup.mk'_surjective _ c
  rw [← map_nsmul, sPicMk_eq_zero_iff] at hc
  obtain ⟨a, ha⟩ := hc
  obtain ⟨x, hx⟩ := exists_divAbove_eq (Ω := Ω) S hN hNS D a ha
  exact ⟨invariantsToH1 S (sInvariantToInvariants S (Additive.ofMul x)),
    by rw [h1SUnitsToSPic_apply, hx]⟩

theorem exists_h1SUnitsToSPic_eq_of_pow {n : ℕ} (hn : n ≠ 0)
    (hnS : ∀ v ∉ S, ((n : ℕ) : 𝓞 F) ∉ v.asIdeal) (c : sPic S) (k : ℕ) (hc : n ^ k • c = 0) :
    ∃ h, h1SUnitsToSPic (Ω := Ω) S h = c := by
  refine exists_h1SUnitsToSPic_eq S (pow_ne_zero k hn) (fun v hv h => hnS v hv ?_) c hc
  rw [Nat.cast_pow] at h
  exact v.isPrime.mem_of_pow_mem k h

end H1

section KummerPic

variable {F Ω : Type u} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]
  [IsSepClosed Ω]
variable (S : Set (HeightOneSpectrum (𝓞 F))) (n : ℕ) [NeZero n]
  (hnS : ∀ v ∉ S, ((n : ℕ) : 𝓞 F) ∉ v.asIdeal)

instance isDiscreteRep_sUnitsKummerSequence_X₁ :
    IsDiscreteRep (sUnitsKummerSequence S (maxUnramifiedOutside F Ω S) n).X₁ :=
  inferInstanceAs (IsDiscreteRep (galRootsOfUnity.{u} F (maxUnramifiedOutside F Ω S) n))

instance isDiscreteRep_sUnitsKummerSequence_X₂ :
    IsDiscreteRep (sUnitsKummerSequence S (maxUnramifiedOutside F Ω S) n).X₂ :=
  inferInstanceAs (IsDiscreteRep (galSUnits S (maxUnramifiedOutside F Ω S)))

instance isDiscreteRep_sUnitsKummerSequence_X₃ :
    IsDiscreteRep (sUnitsKummerSequence S (maxUnramifiedOutside F Ω S) n).X₃ :=
  inferInstanceAs (IsDiscreteRep (galSUnits S (maxUnramifiedOutside F Ω S)))

omit [IsGalois F Ω] [IsSepClosed Ω] [NeZero n] in
theorem invariantsFunctor_map_nsmul_apply
    (w : (galSUnits S (maxUnramifiedOutside F Ω S)).ρ.invariants) :
    ((Rep.invariantsFunctor (ULift.{u} ℤ) (galUnramifiedOutside F Ω S)).map
      (n • 𝟙 (galSUnits S (maxUnramifiedOutside F Ω S)))).hom w = n • w := by
  apply Subtype.ext
  change (n • 𝟙 (galSUnits S (maxUnramifiedOutside F Ω S))).hom w.1 = _
  rw [nsmul_id_hom_apply]
  rfl

include hnS

noncomputable def kummerSUnitsHom :
    Additive (S.unit F) →+ cohomology (galRootsOfUnity.{u} F (maxUnramifiedOutside F Ω S) n) 1 :=
  ((δ (sUnitsKummerSequence_shortExact (Ω := Ω) S n hnS) 0 1 rfl).hom.toAddMonoidHom.comp
    (H0Iso (sUnitsKummerSequence S (maxUnramifiedOutside F Ω S) n).X₃).inv.hom.toAddMonoidHom).comp
    (sUnitsToInvariants S (maxUnramifiedOutside F Ω S))

noncomputable def kummerPicHom :
    cohomology (galRootsOfUnity.{u} F (maxUnramifiedOutside F Ω S) n) 1 →+ sPic S :=
  (h1SUnitsToSPic (Ω := Ω) S).comp
    (cohomologyMap (sUnitsKummerSequence S (maxUnramifiedOutside F Ω S) n).f 1).hom.toAddMonoidHom

theorem kummerSUnitsHom_eq_zero_iff (a : Additive (S.unit F)) :
    kummerSUnitsHom (Ω := Ω) S n hnS a = 0 ↔ ∃ b, n • b = a := by
  refine (δ_H0Iso_inv_eq_zero_iff (sUnitsKummerSequence_shortExact (Ω := Ω) S n hnS) _).trans ?_
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨b, rfl⟩ := sUnitsToInvariants_surjective S (maxUnramifiedOutside F Ω S) w
    refine ⟨b, sUnitsToInvariants_injective S (maxUnramifiedOutside F Ω S) ?_⟩
    rw [map_nsmul]
    refine Eq.trans ?_ hw
    exact (invariantsFunctor_map_nsmul_apply (Ω := Ω) S n _).symm
  · rintro ⟨b, rfl⟩
    refine ⟨sUnitsToInvariants S (maxUnramifiedOutside F Ω S) b, ?_⟩
    exact (invariantsFunctor_map_nsmul_apply (Ω := Ω) S n _).trans (map_nsmul _ _ _).symm

theorem kummerPicHom_eq_zero_iff (y : cohomology (galRootsOfUnity.{u} F (maxUnramifiedOutside F Ω S) n) 1) :
    kummerPicHom (Ω := Ω) S n y = 0 ↔ ∃ a, kummerSUnitsHom (Ω := Ω) S n hnS a = y := by
  have hK := sUnitsKummerSequence_shortExact (Ω := Ω) S n hnS
  constructor
  · intro hy
    have h0 : (cohomologyMap (sUnitsKummerSequence S (maxUnramifiedOutside F Ω S) n).f 1).hom y = 0 :=
      h1SUnitsToSPic_injective S (hy.trans (map_zero _).symm)
    obtain ⟨z, hz⟩ := (ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₁ hK 0 1 rfl) y h0
    obtain ⟨b, hb⟩ := sUnitsToInvariants_surjective S (maxUnramifiedOutside F Ω S)
      ((H0Iso (sUnitsKummerSequence S (maxUnramifiedOutside F Ω S) n).X₃).hom.hom z)
    refine ⟨b, ?_⟩
    change (δ hK 0 1 rfl).hom ((H0Iso _).inv.hom (sUnitsToInvariants S _ b)) = y
    rw [hb, H0Iso_inv_hom_apply]
    exact hz
  · rintro ⟨a, rfl⟩
    have h0 := congrArg (fun φ => φ.hom ((H0Iso (sUnitsKummerSequence S (maxUnramifiedOutside F Ω S) n).X₃).inv.hom
      (sUnitsToInvariants S (maxUnramifiedOutside F Ω S) a))) (δ_comp hK 0 1 rfl)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply] at h0
    exact (congrArg (h1SUnitsToSPic (Ω := Ω) S) h0).trans (map_zero _)

theorem mem_range_kummerPicHom_iff (c : sPic S) :
    (∃ y, kummerPicHom (Ω := Ω) S n y = c) ↔ n • c = 0 := by
  have hK := sUnitsKummerSequence_shortExact (Ω := Ω) S n hnS
  have hg : ∀ h : cohomology (galSUnits S (maxUnramifiedOutside F Ω S)) 1,
      (cohomologyMap (sUnitsKummerSequence S (maxUnramifiedOutside F Ω S) n).g 1).hom h = n • h :=
    fun h => cohomologyMap_nsmul_id_apply (galSUnits S (maxUnramifiedOutside F Ω S)) n 1 h
  constructor
  · rintro ⟨y, rfl⟩
    have h1 := cohomologyMap_g_cohomologyMap_f_apply (S := sUnitsKummerSequence S (maxUnramifiedOutside F Ω S) n) 1 y
    have h1' := (hg _).symm.trans h1
    have h2 := congrArg (h1SUnitsToSPic (Ω := Ω) S) h1'
    exact (map_nsmul (h1SUnitsToSPic (Ω := Ω) S) n _).symm.trans (h2.trans (map_zero _))
  · intro hc
    obtain ⟨h, rfl⟩ := exists_h1SUnitsToSPic_eq (Ω := Ω) S (NeZero.ne n) hnS c hc
    have hh : n • h = 0 := h1SUnitsToSPic_injective S (by rw [map_nsmul, hc, map_zero])
    obtain ⟨y, hy⟩ := exists_cohomologyMap_f_eq hK 1 h ((hg h).trans hh)
    exact ⟨y, congrArg (h1SUnitsToSPic (Ω := Ω) S) hy⟩

end KummerPic

section BaseChange

variable {F L E : Type u} [Field F] [NumberField F] [Field L] [NumberField L] [Field E]
  [Algebra F L] [Algebra F E] [Algebra L E] [IsScalarTower F L E]
variable (S : Set (HeightOneSpectrum (𝓞 F)))

theorem isIntegral_integer_iff_placesOver (x : E) :
    IsIntegral (S.integer F) x ↔
      IsIntegral ((placesOver S : Set (HeightOneSpectrum (𝓞 L))).integer L) x := by
  constructor
  · intro hx
    let f : S.integer F →+* (placesOver S : Set (HeightOneSpectrum (𝓞 L))).integer L :=
      ((algebraMap F L).comp (S.integer F).val.toRingHom).codRestrict _
        fun r w hw => valuation_algebraMap_integer_le_one S hw r
    exact IsIntegral.map_of_comp_eq f (RingHom.id E) (by
      ext r
      exact (IsScalarTower.algebraMap_apply F L E (r : F)).symm) hx
  · intro hx
    let C := integralClosure (S.integer F) E
    let f : (placesOver S : Set (HeightOneSpectrum (𝓞 L))).integer L →+* C :=
      ((algebraMap L E).comp
        ((placesOver S : Set (HeightOneSpectrum (𝓞 L))).integer L).val.toRingHom).codRestrict
        C.toSubring fun c => by
          have hc : IsIntegral (S.integer F) (c : L) :=
            isIntegral_integer_of_valuation_le_one S fun w hw => c.2 w hw
          exact hc.map ((IsScalarTower.toAlgHom F L E).restrictScalars (S.integer F))
    have hxC : IsIntegral C (RingHom.id E x) := IsIntegral.map_of_comp_eq f (RingHom.id E)
      (by ext c; rfl) hx
    have hmem : x ∈ integralClosure C E := hxC
    rw [integralClosure_idem, Algebra.mem_bot] at hmem
    obtain ⟨c, rfl⟩ := hmem
    exact c.2

theorem sUnitsOf_placesOver_eq :
    sUnitsOf (placesOver S : Set (HeightOneSpectrum (𝓞 L))) E = sUnitsOf S E := by
  ext x
  rw [mem_sUnitsOf, mem_sUnitsOf, isIntegral_integer_iff_placesOver (L := L) S,
    isIntegral_integer_iff_placesOver (L := L) S]

end BaseChange

end GroundTheory.ProfCoh
