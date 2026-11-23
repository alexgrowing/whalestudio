import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CentralResidueGroups.CcEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VWOfOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAcross

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open private cc_ex from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CentralResidueGroups.CcEx
open UpperTheory.GalN.V
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Z.Bc
theorem UpperTheory.GalN.V.isAutomorphicOverImagQuad_of_restriction_aut_irr (H : _root_.UpperTheory.V.Af.HypothesesH') (hS : SolC) (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
    (K L : IntermediateField ℚ Ω) [NumberField K] [NumberField L] [IsCMField K] [IsCMField L] (hle : K ≤ L)
    (hK : Module.finrank ℚ K = 2) (hgal : IsGalois ℚ L) (hsol : IsSolvable (L ≃ₐ[ℚ] L)) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (n : ℕ) (hn : 1 ≤ n) (r : G ℚ Ω →* GL (Fin n) (Qbar l)) (θ : G ℚ Ω →* (Qbar l)ˣ) (hr : Continuous r) (hθ : IsAlgChar ι θ)
    (hd : DualTw r θ) (hirr : IsIrr (r.comp (resG ℚ L Ω))) (haut : IsAut ι (r.comp (resG ℚ L Ω))) : IsAutomorphicOverImagQuad ι r := by
  letI : Algebra K L := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  haveI : IsScalarTower K L Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower ℚ K L := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  haveI : IsGalois K L := IsGalois.tower_top_of_isGalois ℚ K L
  haveI : Group.IsSolvable (L ≃ₐ[ℚ] L) := hsol
  have s2 : IsSolvable (L ≃ₐ[K] L) :=
    Group.isSolvable_of_isSolvable_injective (f := (AlgEquiv.restrictScalarsHom ℚ : (L ≃ₐ[K] L) →* (L ≃ₐ[ℚ] L)))
      (AlgEquiv.restrictScalars_injective ℚ)
  have e : (r.comp (resG ℚ K Ω)).comp (resG K L Ω) = r.comp (resG ℚ L Ω) := rfl
  have i2 : IsIrr ((r.comp (resG ℚ K Ω)).comp (resG K L Ω)) := e ▸ hirr
  have i1 : IsIrr (r.comp (resG ℚ K Ω)) := (UpperTheory.galoisRep_irreducibility_criterion.1 _ _ _ n _).1 _ i2
  obtain ⟨c, hc⟩ := cc_ex Ω
  obtain ⟨P, hP⟩ := id hd
  have hp : IsPairing c (r.comp (resG ℚ K Ω)) (θ.comp (resG ℚ K Ω)) (P * r c⁻¹) := fun s s' h => by
    have h' : resG ℚ K Ω s' = c * resG ℚ K Ω s * c⁻¹ := h
    have e0 : r c⁻¹ * r (resG ℚ K Ω s') = r (resG ℚ K Ω s) * r c⁻¹ := by rw [h', ← map_mul, ← map_mul]; congr 1; group
    have e' := congrArg Units.val e0
    have h1 := hP (resG ℚ K Ω s)
    simp only [Units.val_mul, MonoidHom.comp_apply] at e' ⊢
    rw [← Matrix.smul_mul, ← h1]
    simp only [Matrix.mul_assoc, e']
  refine _root_.UpperTheory.GalN.V.ofOne0_alt H third (_root_.UpperTheory.V.Z.Bc.across_alt H hS biQuad) K Ω hK l ι n hn r θ hθ hd i1 ?_
  exact (hS ℚ K L Ω s2 ⟨inferInstance, Or.inr ⟨hK, inferInstance⟩⟩ inferInstance inferInstance l ι n hn _ θ
    (hr.comp (continuous_restrictScalarsHom ℚ K Ω)) i2 hθ (Ws.auSign _) ⟨c, _, hc, hp⟩).2 (e ▸ haut)
end
