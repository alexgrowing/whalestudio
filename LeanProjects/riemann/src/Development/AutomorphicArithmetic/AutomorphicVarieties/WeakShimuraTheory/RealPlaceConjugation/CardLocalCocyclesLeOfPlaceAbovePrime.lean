import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RbUVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.ExistsZmodPrimeRepresentationOfTorsion
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.LocalH1FiniteModL
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.CocycleCardEulerFormula

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

theorem UpperTheory.V.Ws.card_localCocycles_le_of_place_above_prime :
    LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [Finite M], (∀ m : M, l • m = 0) → ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) (ρ : Representation R (Dec (F := F) A) M), IsPlaceOver A v → ((l : ℕ) : 𝓞 F) ∈ v.asIdeal → (∀ m, IsLocallyConstant fun g => ρ g m) → CardLe (cocOff ρ ∅) (Nat.card M ^ (2 + locDeg v)) := by
  intro hF hT hE F Ω _ _ _ _ _ l _ R M _ _ _ _ hl A v ρ hA hv hρ
  obtain ⟨inst, ρ', hρ'⟩ := exists_zmod_prime_representation_of_torsion l (Dec (F := F) A) R M hl ρ
  letI : TopologicalSpace M := ⊥
  haveI : DiscreteTopology M := ⟨rfl⟩
  have hc : ReciprocityTheory.Gal.ContAction ρ' := by
    unfold ReciprocityTheory.Gal.ContAction
    rw [continuous_prod_of_discrete_right]
    intro m
    simp only [hρ']
    exact (hρ m).continuous
  obtain ⟨f1, h1⟩ := local_h1_finite_mod_l hF hT hE F Ω l M A v ρ' hA hc
  obtain ⟨fz, hz⟩ := cocycle_card_euler_formula _ _ M ρ' hc f1
  rw [if_pos hv] at h1
  have h0 : 0 < Nat.card (H0 ρ') := by
    haveI : Finite (H0 ρ') := Subtype.finite
    haveI : Nonempty (H0 ρ') := ⟨0⟩
    exact Nat.card_pos
  have hZ : CardLe (Z1 ρ') (Nat.card M ^ (2 + locDeg v)) := by
    refine ⟨fz, Nat.le_of_mul_le_mul_right ?_ h0⟩
    rw [hz]
    calc Nat.card (H1 ρ') * Nat.card M
        ≤ Nat.card (H0 ρ') * Nat.card M ^ (1 + locDeg v) * Nat.card M := Nat.mul_le_mul_right _ h1
      _ = Nat.card M ^ (2 + locDeg v) * Nat.card (H0 ρ') := by ring
  have hmem : ∀ z : cocOff ρ ∅, z.1 ∈ Z1 ρ' := fun z =>
    (mem_Z1_iff_cocycle ρ' _).2 ⟨z.2.1.continuous, fun g h => by rw [hρ']; exact z.2.2.1 g h⟩
  exact hZ.of_injective (fun z => ⟨z.1, hmem z⟩) fun a b h => Subtype.ext (congrArg (fun z : Z1 ρ' => z.1) h)
