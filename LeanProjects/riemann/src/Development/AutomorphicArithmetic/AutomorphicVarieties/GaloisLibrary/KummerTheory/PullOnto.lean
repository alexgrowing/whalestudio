import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ClPullApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ArtKer
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ArtFrob
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ArtSurj
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PullMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ToGalDict
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PlaceDict

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

theorem UpperTheory.V.Kum.pullOnto :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (U : Subgroup (G F Ω)) (hU : U ≤ galOf F K Ω) (N : ℕ) (R M : Type) [CommRing R] [AddCommGroup M] [Module R M], N ≠ 0 → galOf F K Ω ≤ U → (IsTotallyComplex K ∨ ∀ m : M, 2 • m = 0 → m = 0) → (ClDual K N R M).map (clPull K hU R M) = XDual N U R M := by
  intro F Ω _ _ _ _ _ K _ _ _ _ _ _ U hU N R M _ _ _ hN hU' hK
  refine le_antisymm (pullMem F Ω K U hU N R M hN).1 fun φ hφ => ?_
  obtain ⟨hlc, hadd, hI, hD⟩ := hφ
  obtain ⟨hDec, hIne, -, -⟩ := toGalDict F Ω K U hU
  obtain ⟨hE, -, -⟩ := galEmbTop F K Ω
  let ι : G K Ω →* U := (galEmb F K Ω).codRestrict U fun σ => hU' (galEmb_mem F K Ω σ)
  have hι : Continuous ι := hE.continuous.subtype_mk _
  have h1 : ∀ σ, toGal K hU (ι σ) = σ := fun σ => AlgEquiv.ext fun x => rfl
  have h2 : ∀ u, ι (toGal K hU u) = u := fun u => Subtype.ext (AlgEquiv.ext fun x => rfl)
  let φ' : U →* Multiplicative M := MonoidHom.mk' (fun u => Multiplicative.ofAdd (φ u)) fun a b => by
    rw [hadd, ofAdd_add]
  let χ : G K Ω →* Multiplicative M := φ'.comp ι
  have hχ : ∀ σ, χ σ = 1 ↔ φ (ι σ) = 0 := fun σ => Iff.rfl
  have hker : (artCl K Ω).ker ≤ χ.ker := by
    refine artKer K Ω (Multiplicative M) χ ?_ (fun A σ hσ => ?_) fun c hc => ?_
    · exact (hlc.comp_continuous hι).isOpen_fiber 0
    · exact (hχ σ).2 (hI A _ ((hIne A _).1 ((h1 σ).symm ▸ hσ)))
    · obtain ⟨j, hj⟩ := hc
      rcases hK with hK | hK
      · refine absurd ?_ (InfinitePlace.not_isReal_iff_isComplex.2
          (hK.isComplex (InfinitePlace.mk (j.comp (algebraMap K Ω)))))
        rw [InfinitePlace.isReal_mk_iff, ComplexEmbedding.isReal_iff]
        ext x
        have := hj (algebraMap K Ω x)
        rw [show c.toRingEquiv (algebraMap K Ω x) = algebraMap K Ω x from c.commutes x] at this
        exact this.symm
      · have hcc : c * c = 1 := AlgEquiv.ext fun x => j.injective (by
          have e1 := hj (c x)
          have e2 := hj x
          exact e1.trans ((congrArg _ e2).trans (Complex.conj_conj _)))
        have e : χ c * χ c = 1 := by rw [← map_mul, hcc, map_one]
        refine (hχ c).2 (hK _ ?_)
        rw [two_nsmul]
        exact e
  let θ := MonoidHom.liftOfSurjective (artCl K Ω) (artSurj K Ω).1 ⟨χ, hker⟩
  have hθ : ∀ σ, θ (artCl K Ω σ) = χ σ := fun σ =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨χ, hker⟩ σ
  refine ⟨fun c => Multiplicative.toAdd (θ c), ⟨fun a b => congrArg Multiplicative.toAdd (θ.map_mul a b), fun v hv => ?_⟩, funext fun u => ?_⟩
  · obtain ⟨A, hA⟩ := exists_isPlaceOver Ω v
    obtain ⟨σ, hσ⟩ := exists_isFrob hA
    show Multiplicative.toAdd (θ (primeCl v)) = 0
    rw [← artFrob K Ω A v σ hA hσ, hθ]
    exact hD A (((placeDict K Ω).2.2.2 A v N hA).2 hv) _ ((hDec A _).1 ((h1 σ).symm ▸ hσ.1))
  · rw [clPull_apply, hθ]
    exact congrArg φ (h2 u)
