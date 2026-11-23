import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.ExistsPlaceAbovePrime
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.CuspUnique

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Th
section Alg
open Matrix
end Alg
section Gal
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
theorem automorphic_of_gsp4_rigid_solvable_galois (H : _root_.UpperTheory.V.Af.HypothesesH') (K L : IntermediateField ℚ Ω) [NumberField K] [NumberField L] [IsCMField K] [IsCMField L]
    (hle : K ≤ L) (hK : Module.finrank ℚ K = 2) (hgal : IsGalois ℚ L) (hsol : IsSolvable (L ≃ₐ[ℚ] L)) (ι : Qbar l ≃+* ℂ)
    (r : G ℚ Ω →* M4 (Qbar l)) (θ : G ℚ Ω →* (Qbar l)ˣ) (hr : Continuous r.toHomUnits) (hθ : Af.IsAlgChar ι θ)
    (hm : ∀ g, IsGSp (θ g : Qbar l) (r g)) (cc : G ℚ Ω) (hc : Af.IsConjEl cc) (hirr : Af.IsIrr (r.toHomUnits.comp (resQ L)))
    (haut : Af.IsAut ι (r.toHomUnits.comp (resQ K))) : Af.IsAut ι (r.toHomUnits.comp (resQ L)) := by
  letI : Algebra K L := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  haveI : IsScalarTower K L Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower ℚ K L := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  haveI : IsGalois K L := IsGalois.tower_top_of_isGalois ℚ K L
  haveI : Group.IsSolvable (L ≃ₐ[ℚ] L) := hsol
  have s2 : IsSolvable (L ≃ₐ[K] L) :=
    Group.isSolvable_of_isSolvable_injective (f := (AlgEquiv.restrictScalarsHom ℚ : (L ≃ₐ[K] L) →* (L ≃ₐ[ℚ] L)))
      (AlgEquiv.restrictScalars_injective ℚ)
  obtain ⟨P, hP⟩ := auPair r θ hm cc
  have hp : Af.IsPairing cc (r.toHomUnits.comp (Af.resG ℚ K Ω)) (θ.comp (Af.resG ℚ K Ω)) P := fun s s' h => by
    have h' : Af.resG ℚ K Ω s' = cc * Af.resG ℚ K Ω s * cc⁻¹ := h
    have h1 := hP (Af.resG ℚ K Ω s)
    rw [← h'] at h1
    exact h1
  exact (Z.Bc.solQ (_root_.UpperTheory.V.Z.Bc.solC_alt H H.cyc) ℚ K L Ω s2 ⟨inferInstance, Or.inr ⟨hK, inferInstance⟩⟩
    inferInstance inferInstance l ι 4 (by norm_num) (r.toHomUnits.comp (Af.resG ℚ K Ω)) θ
    (hr.comp (Af.continuous_restrictScalarsHom ℚ K Ω)) hirr hθ (auSign _) ⟨cc, _, hc, hp⟩).1 haut
end Gal
section Core
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
end Core
section Rg
open scoped Matrix TensorProduct
section BK
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime]
  {C V : Type} [CommRing C] [Algebra ℚ_[l] C] [AddCommGroup V] [Module C V] [Module ℚ_[l] V]
  [IsScalarTower ℚ_[l] C V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul C V]
end BK
end Rg
end
