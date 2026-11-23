import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem UpperTheory.exists_section_of_integral_surjective_algClosed :
    ∀ (K : Type) [Field K] [IsAlgClosed K] {Y : Scheme.{0}} (g : Y ⟶ Spec (CommRingCat.of K)) [IsIntegralHom g] [Surjective g], ∃ s : Spec (CommRingCat.of K) ⟶ Y, s ≫ g = 𝟙 _ := by
  intro K _ _ Y g _ _
  haveI : IsAffine Y := isAffine_of_isAffineHom g
  obtain ⟨y, -⟩ := g.surjective (IsLocalRing.closedPoint K)
  obtain ⟨x, -, hx⟩ := (isClosed_univ (X := Y)).exists_closed_singleton ⟨y, trivial⟩
  haveI : IsIntegralHom (Y.fromSpecResidueField x ≫ g) := by
    rw [isClosed_singleton_iff_isClosedImmersion] at hx
    infer_instance
  obtain ⟨φ, hφ⟩ : ∃ φ, Spec.map φ = Y.fromSpecResidueField x ≫ g :=
    ⟨_, Spec.map_preimage _⟩
  haveI : IsIso φ := by
    rw [ConcreteCategory.isIso_iff_bijective]
    refine IsAlgClosed.ringHom_bijective_of_isIntegral _ ?_
    rw [← IsIntegralHom.SpecMap_iff, hφ]
    infer_instance
  refine ⟨Spec.map (inv φ) ≫ Y.fromSpecResidueField x, ?_⟩
  rw [Category.assoc, ← hφ, ← Spec.map_comp]
  simp
