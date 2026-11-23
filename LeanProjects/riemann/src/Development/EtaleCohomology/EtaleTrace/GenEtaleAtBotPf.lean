import Development.EtaleCohomology.EtaleTrace.GenEtalePfData

open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.EtaleTrace.Cov.GenEtaleAtBotPf

theorem formallyEtale_of_fraction {A B K : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Algebra A B] [Module.Finite A B] (hinj : Function.Injective (algebraMap A B))
    [Field K] [Algebra B K] [IsFractionRing B K] [Algebra A K] [IsScalarTower A B K]
    [Algebra.FormallyUnramified A K] : Algebra.FormallyEtale A K := by
  have hAK : Function.Injective (algebraMap A K) := by
    rw [IsScalarTower.algebraMap_eq A B K]
    exact (IsFractionRing.injective B K).comp hinj
  have : FaithfulSMul A K := (faithfulSMul_iff_algebraMap_injective A K).mpr hAK
  let := FractionRing.liftAlgebra A K
  have : Algebra.FormallyUnramified (FractionRing A) K :=
    Algebra.FormallyUnramified.of_restrictScalars A _ _
  have : Algebra.EssFiniteType B K := Algebra.EssFiniteType.of_isLocalization K (nonZeroDivisors B)
  have : Algebra.EssFiniteType A K := Algebra.EssFiniteType.comp A B K
  have : Algebra.EssFiniteType (FractionRing A) K := Algebra.EssFiniteType.of_comp A _ _
  have : Algebra.FormallyEtale (FractionRing A) K := Algebra.FormallyEtale.of_formallyUnramified_of_field _ _
  have : Algebra.FormallyEtale A (FractionRing A) :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors A)
  exact Algebra.FormallyEtale.comp A (FractionRing A) K

theorem isEtaleAt_bot {A B K : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Algebra A B] [Module.Finite A B] (hinj : Function.Injective (algebraMap A B))
    [Field K] [Algebra B K] [IsFractionRing B K] [Algebra A K] [IsScalarTower A B K]
    [Algebra.FormallyUnramified A K] :
    ∃ _ : (⊥ : Ideal B).IsPrime, Algebra.IsEtaleAt A (⊥ : Ideal B) := by
  refine ⟨Ideal.isPrime_bot, ?_⟩
  have := formallyEtale_of_fraction (A := A) (B := B) (K := K) hinj
  have : IsLocalization (nonZeroDivisors B) (Localization.AtPrime (⊥ : Ideal B)) := by
    rw [← Ideal.primeCompl_bot]; infer_instance
  let φ : K ≃ₐ[B] Localization.AtPrime (⊥ : Ideal B) :=
    IsLocalization.algEquiv (nonZeroDivisors B) _ _
  exact Algebra.FormallyEtale.of_equiv (φ.restrictScalars A)

theorem genEtaleAtBot : GenEtaleAtBot := by
  intro X P _ _ π U hU hne hU' hfin hinj hun
  haveI : Nonempty U := hne.to_subtype
  have hV : Nonempty (π ⁻¹ᵁ U) := by
    by_contra h
    rw [not_nonempty_iff] at h
    have hb : π ⁻¹ᵁ U = ⊥ := SetLike.ext' (Set.isEmpty_coe_sort.mp h)
    have : Subsingleton Γ(X, π ⁻¹ᵁ U) :=
      CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty hb)
    exact not_subsingleton Γ(P, U) ⟨fun a b => hinj (Subsingleton.elim _ _)⟩
  let _ := (π.app U).hom.toAlgebra
  have hfin' : Module.Finite Γ(P, U) Γ(X, π ⁻¹ᵁ U) := hfin
  have hη : genericPoint X ∈ π ⁻¹ᵁ U :=
    ((genericPoint_spec X).mem_open_set_iff (π ⁻¹ᵁ U).isOpen).mpr (by simpa using hV)
  have hx : π (genericPoint X) ∈ U := hη
  let alS := P.presheaf.algebra_section_stalk ⟨π (genericPoint X), hx⟩
  have hloc := hU.isLocalization_stalk ⟨π (genericPoint X), hx⟩
  have h1 : (P.presheaf.germ U (π (genericPoint X)) hx).hom.FormallyUnramified := by
    have := Algebra.FormallyUnramified.of_isLocalization (Rₘ := P.presheaf.stalk (π (genericPoint X)))
      (hU.primeIdealOf ⟨π (genericPoint X), hx⟩).asIdeal.primeCompl
    exact RingHom.formallyUnramified_algebraMap.mpr this
  have h2 := h1.comp hun
  rw [← CommRingCat.hom_comp, Scheme.Hom.germ_stalkMap] at h2
  let algK : Algebra Γ(P, U) X.functionField := (π.app U ≫ X.presheaf.germ _ _ hη).hom.toAlgebra
  haveI : IsScalarTower Γ(P, U) Γ(X, π ⁻¹ᵁ U) X.functionField := IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.FormallyUnramified Γ(P, U) X.functionField := h2
  have := functionField_isFractionRing_of_isAffineOpen X (π ⁻¹ᵁ U) hU'
  exact isEtaleAt_bot (K := X.functionField) hinj

theorem GenEtaleAtBot_of : GenEtaleAtBot := genEtaleAtBot

end LateralTheory.EtaleTrace.Cov.GenEtaleAtBotPf
