import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IsClassFieldHilbert
import CompanionTheory.AutomorphicTheory.PlaceSeparation.ArtinA

open NumberField IsDedekindDomain IntermediateField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

theorem UpperTheory.V.CF.ineAbs :
    ∀ (K L Ω : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω] [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsAlgClosure K Ω] [IsGalois K L] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 L)), IsPlaceOver A w → (Ine (F := K) A).map (resTo K L Ω) = w.asIdeal.inertia Gal(L/K) := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ _ A w hw
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  haveI : Algebra.IsAlgebraic L Ω := Algebra.IsAlgebraic.tower_top (K := K) L
  haveI : IsAlgClosure L Ω := ⟨inferInstance, inferInstance⟩
  ext τ
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    exact CompanionTheory.FamInh.res_mem_inertia hw hσ
  · intro hτ
    exact CompanionTheory.FamInh.exists_lift_ine hw hτ
