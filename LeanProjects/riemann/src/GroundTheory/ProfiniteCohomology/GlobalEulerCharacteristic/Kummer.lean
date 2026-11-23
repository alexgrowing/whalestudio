import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.KummerSeq
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseChangeModules
import GroundTheory.ProfiniteCohomology.RestrictedRamification.SInvariantToInvariantsEqZeroIff
import GroundTheory.ProfiniteCohomology.RestrictedRamification.SPicFinite
import GroundTheory.GlobalFields.HerbrandQuotients.SUnitsRep
import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.StabilizersFinite
import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.UnitsDefs
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.Additive
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField IsDedekindDomain CategoryTheory IntermediateField

universe u

noncomputable section

section Restrict

variable {F L Ω : Type u} [Field F] [NumberField F] [Field L] [NumberField L] [Field Ω]
  [Algebra F L] [Algebra F Ω] [Algebra L Ω] [IsScalarTower F L Ω] [IsGalois F Ω]
  {S : Set (HeightOneSpectrum (𝓞 F))}
  (hL : ∀ x : L, algebraMap L Ω x ∈ maxUnramifiedOutside F Ω S) [Normal F L]

instance instNormalGsOpenSubgroup :
    (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside F Ω S)).Normal :=
  gsOpenSubgroup_normal hL

theorem ker_gsRestrictGal_le :
    (gsRestrictGal (S := S) hL).ker ≤ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside F Ω S)) :=
  (ker_gsRestrictGal hL).le

end Restrict

section Units

variable {F L Ω : Type u} [Field F] [NumberField F] [Field L] [NumberField L] [Field Ω]
  [Algebra F L] [Algebra F Ω] [Algebra L Ω] [IsScalarTower F L Ω] [IsGalois F Ω]
  {S : Set (HeightOneSpectrum (𝓞 F))}
  (hL : ∀ x : L, algebraMap L Ω x ∈ maxUnramifiedOutside F Ω S)

theorem map_gsEmbedding_mem_sUnitsMax {x : Lˣ}
    (hx : x ∈ (placesOver S : Set (HeightOneSpectrum (𝓞 L))).unit L) :
    Units.map (gsEmbedding hL : L →* maxUnramifiedOutside F Ω S) x ∈ sUnitsMax F Ω S := by
  have hx' := (mem_sUnitsOf_iff_mem_unit (F := F) (L := L) S).2 hx
  refine ⟨?_, ?_⟩
  · exact hx'.1.map ((gsEmbedding hL).restrictScalars (S.integer F))
  · rw [← map_inv]
    exact hx'.2.map ((gsEmbedding hL).restrictScalars (S.integer F))

def sUnitsToGsInvariants :
    Additive ((placesOver S : Set (HeightOneSpectrum (𝓞 L))).unit L) →+
      (Rep.res (gsSubtype S hL) (galSUnitsMax F Ω S)).ρ.invariants where
  toFun x := ⟨Additive.ofMul ⟨Units.map (gsEmbedding hL : L →* maxUnramifiedOutside F Ω S)
      (x.toMul : Lˣ), map_gsEmbedding_mem_sUnitsMax hL x.toMul.2⟩, fun p => by
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Units.ext
    exact (mem_gsOpenSubgroup_iff S hL (p : galUnramifiedOutside F Ω S)).1 p.2 _⟩
  map_zero' := Subtype.ext (Additive.toMul.injective (Subtype.ext (map_one _)))
  map_add' _ _ := Subtype.ext (Additive.toMul.injective (Subtype.ext (map_mul _ _ _)))

theorem coe_sUnitsToGsInvariants_apply
    (x : Additive ((placesOver S : Set (HeightOneSpectrum (𝓞 L))).unit L)) :
    (((Additive.toMul ((sUnitsToGsInvariants hL x : _) : Additive (sUnitsMax F Ω S)) :
      sUnitsMax F Ω S) : (maxUnramifiedOutside F Ω S)ˣ) : maxUnramifiedOutside F Ω S) =
        gsEmbedding hL (((Additive.toMul x : (placesOver S : Set (HeightOneSpectrum (𝓞 L))).unit L) :
          Lˣ) : L) :=
  rfl

theorem sUnitsToGsInvariants_injective : Function.Injective (sUnitsToGsInvariants hL) := by
  intro x y hxy
  have h := congrArg (fun z : (Rep.res (gsSubtype S hL) (galSUnitsMax F Ω S)).ρ.invariants =>
    (((Additive.toMul (z : Additive (sUnitsMax F Ω S)) : sUnitsMax F Ω S) :
      (maxUnramifiedOutside F Ω S)ˣ) : maxUnramifiedOutside F Ω S)) hxy
  simp only [coe_sUnitsToGsInvariants_apply] at h
  exact Additive.toMul.injective (Subtype.ext (Units.ext ((gsEmbedding hL).injective h)))

theorem exists_gsEmbedding_eq_of_forall {y : maxUnramifiedOutside F Ω S}
    (hy : ∀ p ∈ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside F Ω S)), p y = y) :
    ∃ x : L, gsEmbedding hL x = y := by
  have hmem : y ∈ IntermediateField.fixedField
      (IntermediateField.fixingSubgroup (gsEmbedding (S := S) hL).fieldRange) := by
    rw [IntermediateField.mem_fixedField_iff]
    exact fun p hp => hy p hp
  rw [InfiniteGalois.fixedField_fixingSubgroup] at hmem
  obtain ⟨x, hx⟩ := hmem
  exact ⟨x, hx⟩

theorem sUnitsToGsInvariants_surjective : Function.Surjective (sUnitsToGsInvariants hL) := by
  rintro ⟨a, ha⟩
  set u : sUnitsMax F Ω S := Additive.toMul a
  have hfix : ∀ p ∈ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside F Ω S)),
      p ((u : (maxUnramifiedOutside F Ω S)ˣ) : maxUnramifiedOutside F Ω S) =
        ((u : (maxUnramifiedOutside F Ω S)ˣ) : maxUnramifiedOutside F Ω S) := fun p hp =>
    congrArg (fun z : Additive (sUnitsMax F Ω S) =>
      ((((Additive.toMul z : sUnitsMax F Ω S) : (maxUnramifiedOutside F Ω S)ˣ)) :
        maxUnramifiedOutside F Ω S)) (ha ⟨p, hp⟩)
  obtain ⟨x, hx⟩ := exists_gsEmbedding_eq_of_forall hL hfix
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at hx
    exact (u : (maxUnramifiedOutside F Ω S)ˣ).ne_zero hx.symm
  have hxinv : gsEmbedding hL x⁻¹ =
      (((u⁻¹ : sUnitsMax F Ω S) : (maxUnramifiedOutside F Ω S)ˣ) : maxUnramifiedOutside F Ω S) := by
    rw [map_inv₀, hx, Subgroup.coe_inv, Units.val_inv_eq_inv_val]
  have hint : ∀ {z : L}, IsIntegral (S.integer F) (gsEmbedding hL z) → IsIntegral (S.integer F) z :=
    fun h => (isIntegral_algHom_iff ((gsEmbedding hL).restrictScalars (S.integer F))
      (gsEmbedding (S := S) hL).injective).1 h
  have hmem : Units.mk0 x hx0 ∈ (placesOver S : Set (HeightOneSpectrum (𝓞 L))).unit L := by
    refine (mem_sUnitsOf_iff_mem_unit (F := F) (L := L) S).1 ⟨?_, ?_⟩
    · refine hint ?_
      rw [Units.val_mk0, hx]
      exact u.2.1
    · refine hint ?_
      rw [Units.val_inv_eq_inv_val, Units.val_mk0, hxinv]
      exact (u⁻¹).2.1
  refine ⟨Additive.ofMul ⟨Units.mk0 x hx0, hmem⟩, ?_⟩
  apply Subtype.ext
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  exact hx

def gsH0SUnitsEquiv :
    cohomology (Rep.res (gsSubtype S hL) (galSUnitsMax F Ω S)) 0 ≃+
      Additive ((placesOver S : Set (HeightOneSpectrum (𝓞 L))).unit L) :=
  (H0Iso (Rep.res (gsSubtype S hL) (galSUnitsMax F Ω S))).toLinearEquiv.toAddEquiv.trans
    (AddEquiv.ofBijective (sUnitsToGsInvariants hL)
      ⟨sUnitsToGsInvariants_injective hL, sUnitsToGsInvariants_surjective hL⟩).symm

theorem gsEmbedding_gsH0SUnitsEquiv
    (x : cohomology (Rep.res (gsSubtype S hL) (galSUnitsMax F Ω S)) 0) :
    gsEmbedding hL (((Additive.toMul (gsH0SUnitsEquiv hL x) :
        (placesOver S : Set (HeightOneSpectrum (𝓞 L))).unit L) : Lˣ) : L) =
      (((Additive.toMul ((H0Iso (Rep.res (gsSubtype S hL) (galSUnitsMax F Ω S))).hom.hom x :
        Additive (sUnitsMax F Ω S)) : sUnitsMax F Ω S) : (maxUnramifiedOutside F Ω S)ˣ) :
          maxUnramifiedOutside F Ω S) := by
  rw [← coe_sUnitsToGsInvariants_apply]
  have e : sUnitsToGsInvariants hL (gsH0SUnitsEquiv hL x) =
      (H0Iso (Rep.res (gsSubtype S hL) (galSUnitsMax F Ω S))).hom.hom x :=
    AddEquiv.apply_symm_apply (AddEquiv.ofBijective (sUnitsToGsInvariants hL)
      ⟨sUnitsToGsInvariants_injective hL, sUnitsToGsInvariants_surjective hL⟩) _
  rw [e]

variable [Normal F L]

theorem gsH0SUnitsEquiv_cohomologyConj (g : galUnramifiedOutside F Ω S)
    (x : cohomology (Rep.res (gsSubtype S hL) (galSUnitsMax F Ω S)) 0) :
    gsH0SUnitsEquiv hL ((cohomologyConj (galSUnitsMax F Ω S)
        (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside F Ω S)) 0 g).hom x) =
      GroundTheory.Global.sUnitRep (K := F) (placesOver S : Set (HeightOneSpectrum (𝓞 L)))
        (fun τ _ hw => galSmul_mem_placesOver (S := S) τ hw) (gsRestrictGal hL g) (gsH0SUnitsEquiv hL x) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  refine (gsEmbedding (S := S) hL).injective ?_
  show gsEmbedding hL _ = gsEmbedding hL _
  rw [gsEmbedding_gsH0SUnitsEquiv, H0Iso_hom_cohomologyConj, GroundTheory.Global.sUnitRep_apply]
  change _ = gsEmbedding hL ((((GroundTheory.Global.sUnitMap (placesOver S : Set (HeightOneSpectrum (𝓞 L)))
    (fun τ _ hw => galSmul_mem_placesOver (S := S) τ hw) (gsRestrictGal hL g)
    (Additive.toMul (gsH0SUnitsEquiv hL x))) :
      (placesOver S : Set (HeightOneSpectrum (𝓞 L))).unit L) : Lˣ) : L)
  rw [GroundTheory.Global.coe_sUnitMap, gsEmbedding_gsRestrictGal, gsEmbedding_gsH0SUnitsEquiv]
  rfl

theorem conj_gsH0SUnits_eq {l : ℕ} (d : AdditiveFunction.{u} l (L ≃ₐ[F] L))
    [Finite (ModN (Additive ((placesOver S : Set (HeightOneSpectrum (𝓞 L))).unit L)) l)]
    [Finite (TorsN (Additive ((placesOver S : Set (HeightOneSpectrum (𝓞 L))).unit L)) l)] :
    (letI := conjActionOf (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside F Ω S))
        (gsRestrictGal hL) (gsRestrictGal_surjective hL) (ker_gsRestrictGal_le hL)
        (galSUnitsMax F Ω S) 0;
      d.g (cohomology (Rep.res (gsSubtype S hL) (galSUnitsMax F Ω S)) 0)) =
    (letI := sUnitAction (K := F) (placesOver S : Set (HeightOneSpectrum (𝓞 L)))
        (fun τ _ hw => galSmul_mem_placesOver (S := S) τ hw);
      d.g (Additive ((placesOver S : Set (HeightOneSpectrum (𝓞 L))).unit L))) := by
  let := conjActionOf (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside F Ω S))
    (gsRestrictGal hL) (gsRestrictGal_surjective hL) (ker_gsRestrictGal_le hL) (galSUnitsMax F Ω S) 0
  let := sUnitAction (K := F) (placesOver S : Set (HeightOneSpectrum (𝓞 L)))
    (fun τ _ hw => galSmul_mem_placesOver (S := S) τ hw)
  have : Finite (cohomology (Rep.res (gsSubtype S hL) (galSUnitsMax F Ω S)) 0 ⧸
      (gsH0SUnitsEquiv hL).symm.toAddMonoidHom.range) := by
    rw [AddMonoidHom.range_eq_top.2 (gsH0SUnitsEquiv hL).symm.surjective]
    infer_instance
  refine d.g_eq_of_finite_cokernel (gsH0SUnitsEquiv hL).symm.toAddMonoidHom (fun γ b => ?_)
    (gsH0SUnitsEquiv hL).symm.injective
  obtain ⟨g, rfl⟩ := gsRestrictGal_surjective hL γ
  apply (gsH0SUnitsEquiv hL).injective
  change gsH0SUnitsEquiv hL ((gsH0SUnitsEquiv hL).symm _) =
    gsH0SUnitsEquiv hL (gsRestrictGal hL g • (gsH0SUnitsEquiv hL).symm b)
  rw [conjActionOf_smul, gsH0SUnitsEquiv_cohomologyConj, AddEquiv.apply_symm_apply,
    AddEquiv.apply_symm_apply]
  rfl

end Units

section H1

variable {F L Ω : Type u} [Field F] [NumberField F] [Field L] [NumberField L] [Field Ω]
  [Algebra F L] [Algebra F Ω] [Algebra L Ω] [IsScalarTower F L Ω] [IsGalois F Ω]
  {S : Set (HeightOneSpectrum (𝓞 F))}
  (hL : ∀ x : L, algebraMap L Ω x ∈ maxUnramifiedOutside F Ω S)

theorem finite_gsH1SUnits :
    Finite (cohomology (Rep.res (gsSubtype S hL) (galSUnitsMax F Ω S)) 1) := by
  have : IsGalois L Ω := IsGalois.tower_top_of_isGalois F L Ω
  have : Finite (cohomology (galSUnitsMax L Ω (placesOver S : Set (HeightOneSpectrum (𝓞 L)))) 1) :=
    Finite.of_injective _ (h1SUnitsToSPic_injective (F := L) (Ω := Ω)
      (placesOver S : Set (HeightOneSpectrum (𝓞 L))))
  exact Finite.of_equiv _ (gsSUnitsCohomologyIso S hL 1).toLinearEquiv.toEquiv

end H1

end

end GroundTheory.ProfCoh
