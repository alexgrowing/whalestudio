import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.WdDefs
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPotSemistableIndependentOfInducingEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamAboveLIndependentLocalEmbeddingStatement
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CycFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.WeilDeligneMonodromyUpperTriangular
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.TridiagonalWeilDeligne
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.WeilDeligneTriangularizable
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CyclotomicWeilCharProperties
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ContinuousCharacterCompactUnitValues
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CrystallinePeriodRingProperties
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GaloisRepValuesInFiniteExtension
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GaloisRepresentationModelOverFiniteExtension

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Module
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Wd

private theorem cont_diag {Γ : Type} [Group Γ] [TopologicalSpace Γ] {l : ℕ} [Fact l.Prime] {n : ℕ}
    {r : Γ →* GL (Fin n) (Qbar l)} (hr : Continuous r) {H : Subgroup Γ} {κ : Fin n → ↥H →* (Qbar l)ˣ}
    (hf : IsFlagOn r H κ) (i : Fin n) : Continuous fun s => (κ i s : Qbar l) := by
  obtain ⟨g, hg⟩ := hf
  have h1 : Continuous fun s : ↥H => (g * r s * g⁻¹ : GL (Fin n) (Qbar l)) :=
    (continuous_const.mul (hr.comp continuous_subtype_val)).mul continuous_const
  exact ((Units.continuous_val.comp h1).matrix_elem i i).congr fun s => (hg s).2 i

private theorem transport_rho {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {w : HeightOneSpectrum (𝓞 F)} {A : ValuationSubring Ω} {h : IsPlaceOver A w} {W : Type} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] {n : ℕ} (a : WDRep h W) (b : Basis (Fin n) ℂ W) (σ : ↥(Weil h))
    (X : Matrix (Fin n) (Fin n) ℂ) (hX : LinearMap.toMatrix b b (a.ρ σ) = X) :
    (a.transport b.equivFun).ρ σ = Matrix.toLin' X := by
  refine LinearMap.ext fun v => ?_
  obtain ⟨x, rfl⟩ := b.equivFun.surjective v
  change b.equivFun (a.ρ σ (b.equivFun.symm (b.equivFun x))) = _
  rw [LinearEquiv.symm_apply_apply, Matrix.toLin'_apply, ← hX]
  exact (LinearMap.toMatrix_mulVec_repr b b (a.ρ σ) x).symm
