import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.FixedPointCriteria.IntDown
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.SplitUnitElements.IntE

open QuadraticAlgebra Matrix UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

theorem UpperTheory.V.Z.Sym.Loc.One.princ :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
        (∃ u : Oˣ, algebraMap O K u = τ ^ 2 - 4) → ∀ S : Set (Etau K τ), IsLat O τ S → (∀ x ∈ S, ω * x ∈ S) →
        ∃ u : (Etau K τ)ˣ, ∀ x, x ∈ S ↔ IsIntegral O (((u⁻¹ : (Etau K τ)ˣ) : Etau K τ) * x) := by
  intro O K _ _ _ _ _ Δ τ hl hu S hS hω
  obtain ⟨hτ, -, -, -⟩ := One.intE O K Δ τ hl hu
  have hne : τ ^ 2 - 4 ≠ 0 := by
    obtain ⟨v, hv⟩ := hu
    rw [← hv]
    exact (Units.map (algebraMap O K).toMonoidHom v).ne_zero
  have hg : PK.Gen1 O (ω : Etau K τ) := by
    refine ⟨?_, ?_, ?_⟩
    · simpa [QuadraticAlgebra.trace] using hτ
    · exact ⟨1, by simp [QuadraticAlgebra.norm]⟩
    · simpa using hu
  exact PK.Gen1.princ hl hne hg hS hω
