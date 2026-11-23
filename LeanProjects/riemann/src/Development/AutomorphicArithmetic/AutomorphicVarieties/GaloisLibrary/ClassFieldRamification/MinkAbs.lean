import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IsClassFieldHilbert
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IneAbs
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.MinkGen

open NumberField IsDedekindDomain IntermediateField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

private theorem minkGen' (K : Type) [Field K] [NumberField K] [inst : Algebra ℚ K] [IsGalois ℚ K] :
    (⨆ w : HeightOneSpectrum (𝓞 K), w.asIdeal.inertia Gal(K/ℚ)) = ⊤ := by
  obtain rfl : inst = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  exact UpperTheory.V.CF.minkGen K

private theorem top_of_gen (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (hgen : ∀ (L : Type) [Field L] [NumberField L] [Algebra K L] [IsGalois K L],
      (⨆ w : HeightOneSpectrum (𝓞 L), w.asIdeal.inertia Gal(L/K)) = ⊤)
    (V : Subgroup (G K Ω)) (hV : IsOpen (V : Set (G K Ω))) (hI : ∀ A : ValuationSubring Ω, Ine (F := K) A ≤ V) :
    V = ⊤ := by
  obtain ⟨L, hfin, hnorm, hL⟩ := (krullTopology_mem_nhds_one_iff_of_normal K Ω _).1 (hV.mem_nhds V.one_mem)
  haveI : NumberField L := NumberField.of_module_finite K L
  haveI : IsGalois K L := {}
  have hker : (resTo K L Ω).ker ≤ V := by
    have h : (resTo K L Ω).ker = L.fixingSubgroup := IntermediateField.restrictNormalHom_ker L
    rw [h]
    exact hL
  have hmap : V.map (resTo K L Ω) = ⊤ := by
    rw [eq_top_iff, ← hgen L]
    refine iSup_le fun w => ?_
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    rw [← UpperTheory.V.CF.ineAbs K L Ω A w hA]
    exact Subgroup.map_mono (hI A)
  have h := Subgroup.comap_map_eq_self hker
  rw [hmap, Subgroup.comap_top] at h
  exact h.symm

theorem UpperTheory.V.CF.minkAbs :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (V : Subgroup (G ℚ Ω)), IsOpen (V : Set (G ℚ Ω)) → (∀ A : ValuationSubring Ω, Ine (F := ℚ) A ≤ V) → V = ⊤ := by
  intro Ω _ _ _ V hV hI
  exact top_of_gen ℚ Ω (fun L _ _ _ _ => minkGen' L) V hV hI
