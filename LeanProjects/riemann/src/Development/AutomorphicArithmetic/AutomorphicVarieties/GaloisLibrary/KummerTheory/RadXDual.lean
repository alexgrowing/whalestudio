import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.RadExists
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ToGalDict
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.DvdOfIne

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

theorem UpperTheory.V.Kum.radXDual :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (U : Subgroup (G F Ω)) (n : ℕ) [NeZero n] (N : ℕ) (ζ : K), U = galOf F K Ω → IsPrimitiveRoot ζ n → (∀ φ ∈ XDual N U (ZMod n) (ZMod n), ∃ (β : Ω) (a : Kˣ), IsRad (algebraMap K Ω ζ) U φ β ∧ β ^ n = algebraMap K Ω a ∧ a ∈ SelK (∅ : Set (HeightOneSpectrum (𝓞 K))) n) ∧
    ∀ (φ : U → ZMod n) (β β' : Ω), IsRad (algebraMap K Ω ζ) U φ β → IsRad (algebraMap K Ω ζ) U φ β' → ∃ c : Kˣ, β' = algebraMap K Ω c * β := by
  intro F Ω _ _ _ _ _ K _ _ _ _ _ _ U n _ N ζ hU hζ
  subst hU
  have hζ' : IsPrimitiveRoot (algebraMap K Ω ζ) n := hζ.map_of_injective (algebraMap K Ω).injective
  obtain ⟨-, hI, -, hH⟩ := toGalDict F Ω K (galOf F K Ω) le_rfl
  obtain ⟨hH, -⟩ := hH le_rfl
  let s : G K Ω → galOf F K Ω := fun σ => ⟨galEmb F K Ω σ, galEmb_mem F K Ω σ⟩
  have hs : ∀ σ, toGal K le_rfl (s σ) = σ := fun σ => AlgEquiv.ext fun x => rfl
  have hs' : ∀ u, s (toGal K le_rfl u) = u := fun u => Subtype.ext (AlgEquiv.ext fun x => rfl)
  have hsm : ∀ σ τ, s (σ * τ) = s σ * s τ := fun σ τ => Subtype.ext (map_mul (galEmb F K Ω) σ τ)
  have hsc : Continuous s := by
    have e : s = hH.homeomorph.symm := funext fun σ => by
      rw [eq_comm, Homeomorph.symm_apply_eq]
      exact (hs σ).symm
    rw [e]
    exact hH.homeomorph.symm.continuous
  refine ⟨fun φ hφ => ?_, fun φ β β' hβ hβ' => ?_⟩
  · obtain ⟨hlc, hadd, hine, -⟩ := hφ
    obtain ⟨β, a, hβa, hβ⟩ := radExists K Ω n (algebraMap K Ω ζ) (fun _ => 1) (fun σ => φ (s σ)) hζ'
      (fun g => by
        rw [g.commutes, ZMod.val_one_eq_one_mod, hζ'.eq_orderOf, pow_mod_orderOf, pow_one])
      (hlc.comp_continuous hsc) (fun g h => by rw [hsm, hadd, one_mul])
    refine ⟨β, a, ⟨?_, fun u => ?_⟩, hβa, fun v _ => ?_⟩
    · rintro rfl
      rw [zero_pow (NeZero.ne n), eq_comm, map_eq_zero] at hβa
      exact a.ne_zero hβa
    · have := hβ (toGal K le_rfl u)
      rw [hs'] at this
      exact this
    · obtain ⟨A, hA⟩ := exists_isPlaceOver Ω v
      refine dvdOfIne K Ω n A v β a hA hβa fun g hg => ?_
      have h0 : φ (s g) = 0 := hine A (s g) ((hI A (s g)).1 (by rw [hs]; exact hg))
      rw [hβ g, h0, ZMod.val_zero, pow_zero, one_mul]
  · have hz : algebraMap K Ω ζ ≠ 0 := hζ'.ne_zero (NeZero.ne n)
    haveI : IsGalois K Ω := IsAlgClosure.isGalois K Ω
    have hfix : ∀ g : G K Ω, g (β' / β) = β' / β := fun g => by
      have e1 : g β = _ := hβ.2 (s g)
      have e2 : g β' = _ := hβ'.2 (s g)
      rw [map_div₀, e1, e2, mul_div_mul_left _ _ (pow_ne_zero _ hz)]
    obtain ⟨c, hc⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (β' / β)).2 hfix
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [map_zero, eq_comm] at hc
      exact div_ne_zero hβ'.1 hβ.1 hc
    refine ⟨Units.mk0 c hc0, ?_⟩
    rw [Units.val_mk0, hc, div_mul_cancel₀ _ hβ.1]
