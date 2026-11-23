import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.EpsilonEtaTensorDual
open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.sumCount :
    ∀ (R D M : Type) [CommRing R] [Group D] [AddCommGroup M] [Module R M] [Finite M] (ρ : Representation R D M) (b : AddSubgroup M) (Z : AddSubgroup (D → M)), Finite Z → (∀ y ∈ b, (fun g => ρ g y - y) ∈ Z) → Finite ((Bl ρ).toAddSubgroup ⊔ Z : AddSubgroup (D → M)) ∧ Nat.card ((Bl ρ).toAddSubgroup ⊔ Z : AddSubgroup (D → M)) * Nat.card b ≤ Nat.card M * Nat.card Z := by
  intro R D M _ _ _ _ _ ρ b Z hZ hb
  let d : M →ₗ[R] (D → M) := LinearMap.pi fun g => ρ g - LinearMap.id
  have hd : ∀ y, d y = fun g => ρ g y - y := fun y => rfl
  let φ : M × Z →+ (D → M) := d.toAddMonoidHom.coprod Z.subtype
  have hφ : ∀ p : M × Z, φ p = d p.1 + p.2 := fun p => rfl
  have hr : φ.range = (Bl ρ).toAddSubgroup ⊔ Z := by
    apply le_antisymm
    · rintro _ ⟨p, rfl⟩
      rw [hφ]
      exact AddSubgroup.add_mem_sup (show d p.1 ∈ (Bl ρ).toAddSubgroup from ⟨p.1, rfl⟩) p.2.2
    · refine sup_le ?_ ?_
      · rintro _ ⟨y, rfl⟩
        exact ⟨(y, 0), by rw [hφ]; exact add_zero _⟩
      · intro z hz
        exact ⟨(0, ⟨z, hz⟩), by rw [hφ]; simp⟩
  rw [← hr]
  have hfin : Finite φ.range := Finite.of_surjective _ φ.rangeRestrict_surjective
  refine ⟨hfin, ?_⟩
  have h1 : Nat.card (M × Z) = Nat.card φ.range * Nat.card φ.ker := by
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup φ.ker,
      Nat.card_congr (QuotientAddGroup.quotientKerEquivRange φ).toEquiv]
  have h2 : Nat.card b ≤ Nat.card φ.ker := by
    let ι : b → φ.ker := fun y => ⟨(y.1, -⟨fun g => ρ g y.1 - y.1, hb y.1 y.2⟩), by
      rw [AddMonoidHom.mem_ker, hφ, hd]
      exact add_neg_cancel _⟩
    refine Nat.card_le_card_of_injective ι fun y y' h => ?_
    exact Subtype.ext (congrArg (fun p : φ.ker => p.1.1) h)
  rw [← Nat.card_prod M Z, h1]
  exact Nat.mul_le_mul_left _ h2
