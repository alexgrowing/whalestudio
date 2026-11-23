import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsAlgChar

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af

theorem UpperTheory.V.Z.Bc.exists_quad (L Ω : Type) [Field L] [NumberField L] [IsGalois ℚ L] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra L Ω]
    (η : G ℚ Ω →* ℤˣ) (c : G ℚ Ω) (hc : IsConjEl c) (hη : η c = -1) (hL : ∀ s : G L Ω, η (resG ℚ L Ω s) = 1) :
    ∃ K : IntermediateField ℚ L, Module.finrank ℚ K = 2 ∧ IsCMField K := by
  haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
  let p : (Ω ≃ₐ[ℚ] Ω) →* (L ≃ₐ[ℚ] L) := AlgEquiv.restrictNormalHom L
  have hp : Function.Surjective p := AlgEquiv.restrictNormalHom_surjective Ω
  have hpx : ∀ (s : Ω ≃ₐ[ℚ] Ω) (x : L), algebraMap L Ω (p s x) = s (algebraMap L Ω x) := fun s x => AlgEquiv.restrictNormal_commutes s L x
  have hk : p.ker ≤ η.ker := fun s hs => hL (AlgEquiv.ofRingEquiv (f := s.toRingEquiv) fun x => by
    have := hpx s x
    rw [show p s = 1 from hs] at this
    exact this.symm)
  let θ : (L ≃ₐ[ℚ] L) →* ℤˣ := p.liftOfSurjective hp ⟨η, hk⟩
  have hθ : ∀ s, θ (p s) = η s := fun s => MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ s
  have hidx : θ.ker.index = 2 := by
    rw [Subgroup.index_ker, show θ.range = ⊤ from eq_top_iff.2 fun u _ => by
      rcases Int.units_eq_one_or u with rfl | rfl
      · exact one_mem _
      · exact ⟨p c, (hθ c).trans hη⟩]
    simp
  have h2 : Module.finrank ℚ (IntermediateField.fixedField θ.ker) = 2 := by
    have h := Module.finrank_mul_finrank ℚ (IntermediateField.fixedField θ.ker) L
    rw [IntermediateField.finrank_fixedField_eq_card, ← IsGalois.card_aut_eq_finrank ℚ L, ← θ.ker.index_mul_card, hidx] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  refine ⟨_, h2, ?_⟩
  set K := IntermediateField.fixedField θ.ker
  haveI : Algebra.IsQuadraticExtension ℚ K := ⟨h2⟩
  obtain ⟨j, hj⟩ := hc
  let φ : K →+* ℂ := j.comp ((algebraMap L Ω).comp (algebraMap K L))
  have hφ : ¬ ComplexEmbedding.IsReal φ := fun h => by
    have : p c ∈ K.fixingSubgroup := (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => by
      apply (algebraMap L Ω).injective
      apply j.injective
      rw [hpx, hj]
      exact RingHom.congr_fun (ComplexEmbedding.isReal_iff.1 h) ⟨x, hx⟩
    rw [IntermediateField.fixingSubgroup_fixedField, MonoidHom.mem_ker, hθ, hη] at this
    exact absurd this (by decide)
  haveI : IsTotallyComplex K := by
    classical
    have h1 := InfinitePlace.card_add_two_mul_card_eq_rank K
    have h3 : 0 < InfinitePlace.nrComplexPlaces K := Fintype.card_pos_iff.2 ⟨⟨InfinitePlace.mk φ, by
      rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_mk_iff]; exact hφ⟩⟩
    exact NumberField.nrRealPlaces_eq_zero_iff.1 (by omega)
  exact IsCMField.ofCMExtension ℚ K
