import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Statement
import ReciprocityTheory.GaloisValuations.Global
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.RealStructures.Imports
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.ImportsBis
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.RamificationIdxEqOneAndInertiaDegEqOne
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.LocalDegreeOne

open scoped Pointwise

theorem main : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (L L' : IntermediateField E Ω) (hL : FiniteDimensional E L) (hL' : FiniteDimensional E L'), L ≤ L' →
    haveI := hL; haveI := hL'; haveI : NumberField L := NumberField.of_module_finite E L
    haveI : NumberField L' := NumberField.of_module_finite E L'
    ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 L)) (v' : HeightOneSpectrum (𝓞 L')),
      IsPlaceOver A v → IsPlaceOver A v' →
      (∀ σ : Ω ≃ₐ[E] Ω, σ ∈ A.decompositionSubgroup E → (∀ x ∈ L, σ x = x) → ∀ x ∈ L', σ x = x) →
      v'.asIdeal.ramificationIdx (𝓞 E) = v.asIdeal.ramificationIdx (𝓞 E) ∧ normV v' = normV v := by
  intro E Ω _ _ _ _ _ L L' hL hL' hLL'
  haveI := hL
  haveI := hL'
  haveI : NumberField L := NumberField.of_module_finite E L
  haveI : NumberField L' := NumberField.of_module_finite E L'
  intro A v v' hv hv' hfix
  letI : Algebra L L' := (IntermediateField.inclusion hLL').toRingHom.toAlgebra
  haveI : IsScalarTower L L' Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower E L L' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsAlgClosure L Ω := ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.tower_top (K := E) L⟩
  haveI : IsAlgClosure L' Ω := ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.tower_top (K := E) L'⟩
  haveI : Module.Finite L L' := Module.Finite.of_restrictScalars_finite E L L'
  haveI : NumberField (IntermediateField.normalClosure L L' Ω) :=
    NumberField.of_module_finite L (IntermediateField.normalClosure L L' Ω)
  haveI : IsAlgClosure (IntermediateField.normalClosure L L' Ω) Ω :=
    ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.tower_top (K := L) (IntermediateField.normalClosure L L' Ω)⟩
  obtain ⟨P, hP⟩ := GlobalTheory.PlaceIsoDec.exists_isPlaceOver_mid (K := L) (L := IntermediateField.normalClosure L L' Ω) hv
  obtain ⟨he, hf⟩ := GlobalTheory.PlaceIsoDec.ramificationIdx_eq_one_and_inertiaDeg_eq_one (K := L') hv hv' hP (by
    intro σ hσ
    have h1 : σ.restrictScalars E ∈ A.decompositionSubgroup E := hσ
    have h2 : ∀ x ∈ L, σ.restrictScalars E x = x := fun x hx => σ.commutes ⟨x, hx⟩
    have h3 := hfix _ h1 h2
    exact ⟨{ σ.toRingEquiv with commutes' := fun y => h3 _ y.2 }, AlgEquiv.ext fun _ => rfl⟩)
  haveI : v'.asIdeal.LiesOver v.asIdeal := GlobalTheory.PlaceIsoDec.liesOver_of_isPlaceOver hv hv'
  constructor
  · rw [Ideal.ramificationIdx_tower (R := 𝓞 E) v.asIdeal v'.asIdeal, he, mul_one]
  · have h := Ideal.absNorm_pow_inertiaDeg v.asIdeal v'.asIdeal
    rw [hf, pow_one] at h
    simp only [normV]
    rw [← Submodule.cardQuot_apply, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, ← Ideal.absNorm_apply, h]

end GlobalTheory.LocalDegreeOne
