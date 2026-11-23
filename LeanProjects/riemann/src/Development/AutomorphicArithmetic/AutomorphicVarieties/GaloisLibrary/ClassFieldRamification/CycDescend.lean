import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IsClassFieldHilbert
import GroundTheory.GlobalFields.TateThesis.Chebotarev
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.CycInertia
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.UnitsGen
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IneFixQ

open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

theorem UpperTheory.V.CF.cycDescend :
    ∀ (a b : ℕ) [NeZero (a * b)] (C : Type) [Field C] [NumberField C] [IsCyclotomicExtension {a * b} ℚ C] (ζ : C) (F : IntermediateField ℚ C), a.Coprime b → IsPrimitiveRoot ζ (a * b) → (∀ p : ℕ, p.Prime → p ∣ b → UnramAt F p) → F ≤ ℚ⟮ζ ^ b⟯ := by
  intro a b _ C _ _ _ ζ F hab hζ hunr
  have hb0 : b ≠ 0 := right_ne_zero_of_mul (NeZero.ne (a * b))
  haveI : IsGalois ℚ C := IsCyclotomicExtension.isGalois {a * b} ℚ C
  set χ := IsCyclotomicExtension.Rat.galEquivZMod (a * b) C with hχ
  have hcomm : ∀ σ τ : Gal(C/ℚ), τ * σ * τ⁻¹ = σ := by
    intro σ τ
    apply χ.injective
    rw [map_mul, map_mul, map_inv, mul_comm (χ τ), mul_assoc, mul_inv_cancel, mul_one]
  haveI : F.fixingSubgroup.Normal := ⟨fun σ hσ τ => by rw [hcomm]; exact hσ⟩
  have hFF : fixedField F.fixingSubgroup = F := IsGalois.fixedField_fixingSubgroup F
  haveI hgF : IsGalois ℚ F := by
    have h := IsGalois.of_fixedField_normal_subgroup F.fixingSubgroup
    rw [hFF] at h
    convert h
    exact Subsingleton.elim _ _
  have hin : ∀ p : ℕ, p.Prime → p ∣ b → ∀ w : HeightOneSpectrum (𝓞 C), (p : 𝓞 C) ∈ w.asIdeal →
      w.asIdeal.inertia Gal(C/ℚ) ≤ F.fixingSubgroup := by
    intro p hp hpb w hw σ hσ
    have hk := (UpperTheory.V.CF.ineFixQ F C p hp).mp (hunr p hp hpb) w hw hσ
    rw [MonoidHom.mem_ker] at hk
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have hc := UpperTheory.V.CF.resTo_commutes ℚ F C σ ⟨x, hx⟩
    rw [hk, AlgEquiv.one_apply] at hc
    exact hc.symm
  have hsup : ⨆ p ∈ b.primeFactors, KStar.Ram.inertiaUnits (a * b) p ≤
      F.fixingSubgroup.map χ.toMonoidHom := by
    refine iSup₂_le fun p hp => ?_
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpb : p ∣ b := Nat.dvd_of_mem_primeFactors hp
    haveI : Fact p.Prime := ⟨hpp⟩
    haveI : (Ideal.span {(p : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hpp).irreducible
    obtain ⟨P, hPm, hPl⟩ :=
      Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 C) (Ideal.span {(p : ℤ)})
    haveI := hPm
    haveI := hPl
    have hpP : (p : 𝓞 C) ∈ P := by
      have h1 : (p : ℤ) ∈ Ideal.span {(p : ℤ)} := Ideal.mem_span_singleton_self _
      rw [Ideal.LiesOver.over (P := P) (p := Ideal.span {(p : ℤ)}), Ideal.under_def,
        Ideal.mem_comap] at h1
      simpa using h1
    let w : HeightOneSpectrum (𝓞 C) := ⟨P, hPm.isPrime, fun h => by
      rw [h, Ideal.mem_bot] at hpP
      exact (Nat.cast_ne_zero.mpr hpp.ne_zero) hpP⟩
    rw [← KStar.Ram.map_inertia_eq p P]
    exact Subgroup.map_mono (hin p hpp hpb w hpP)
  rw [← IsGalois.fixedField_fixingSubgroup ℚ⟮ζ ^ b⟯, IntermediateField.le_iff_le]
  intro σ hσ
  have hfix : σ (ζ ^ b) = ζ ^ b := (IntermediateField.mem_fixingSubgroup_iff _ σ).mp hσ _
    (IntermediateField.mem_adjoin_simple_self ℚ _)
  have hker : χ σ ∈ (ZMod.unitsMap (Dvd.intro b rfl : a ∣ a * b)).ker := by
    rw [MonoidHom.mem_ker, Units.ext_iff, ZMod.unitsMap_val, ZMod.cast_eq_val, Units.val_one]
    rw [map_pow, IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq (a * b) C σ hζ.pow_eq_one,
      ← pow_mul] at hfix
    have hmod : (χ σ).val.val * b ≡ 1 * b [MOD a * b] := by
      rw [one_mul]
      have h2 := (hζ.isOfFinOrder (NeZero.ne _)).pow_inj_mod.mp hfix
      rw [← hζ.eq_orderOf] at h2
      exact h2
    have hk := Nat.ModEq.mul_right_cancel' hb0 hmod
    rw [← Nat.cast_one]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr hk
  have hmem := hsup (UpperTheory.V.CF.unitsGen a b hab hker)
  rw [Subgroup.mem_map] at hmem
  obtain ⟨τ, hτ, hτσ⟩ := hmem
  have hτσ' : τ = σ := χ.injective hτσ
  rwa [hτσ'] at hτ
