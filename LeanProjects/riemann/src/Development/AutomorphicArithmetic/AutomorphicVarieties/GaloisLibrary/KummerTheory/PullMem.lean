import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ClPullApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ToGalDict
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ArtSurj
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ArtIne
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ArtDec
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PlaceDict

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

theorem UpperTheory.V.Kum.pullMem :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (U : Subgroup (G F Ω)) (hU : U ≤ galOf F K Ω) (N : ℕ) (R M : Type) [CommRing R] [AddCommGroup M] [Module R M], N ≠ 0 → (ClDual K N R M).map (clPull K hU R M) ≤ XDual N U R M ∧ (galOf F K Ω ≤ U → Function.Injective (clPull K hU R M)) := by
  intro F Ω _ _ _ _ _ K _ _ _ _ _ _ U hU N R M _ _ _ hN
  obtain ⟨hD, hI, hc, hH⟩ := toGalDict F Ω K U hU
  obtain ⟨hS, hL⟩ := artSurj K Ω
  obtain ⟨-, hP, hT, hA⟩ := placeDict K Ω
  refine ⟨?_, fun h => ?_⟩
  · rintro _ ⟨θ, ⟨hm, hv⟩, rfl⟩
    let θ' : ClassGroup (𝓞 K) →* Multiplicative M := MonoidHom.mk' (fun c => Multiplicative.ofAdd (θ c)) fun a b => by
      rw [hm, ofAdd_add]
    have h1 : θ 1 = 0 := congrArg Multiplicative.toAdd θ'.map_one
    refine ⟨?_, fun a b => ?_, fun A u hu => ?_, fun A hAN u hu => ?_⟩
    · exact (hL.comp_continuous hc).comp θ
    · rw [clPull_apply, clPull_apply, clPull_apply, map_mul, map_mul, hm]
    · rw [clPull_apply, (artIne K Ω).1 A _ ((hI A u).2 hu), h1]
    · obtain ⟨v, hAv⟩ := hP A (hT A N hN hAN)
      have hvN := (hA A v N hAv).1 hAN
      have hmem : artCl K Ω (toGal K hU u) ∈ Subgroup.zpowers (primeCl v) := by
        rw [← artDec K Ω A v hAv]
        exact Subgroup.mem_map_of_mem _ ((hD A u).2 hu)
      have hle : Subgroup.zpowers (primeCl v) ≤ θ'.ker := by
        rw [Subgroup.zpowers_le, MonoidHom.mem_ker]
        exact congrArg Multiplicative.ofAdd (hv v hvN)
      rw [clPull_apply]
      exact congrArg Multiplicative.toAdd (MonoidHom.mem_ker.1 (hle hmem))
  · exact LinearMap.funLeft_injective_of_surjective R M _ (hS.comp (hH h).1.surjective)
