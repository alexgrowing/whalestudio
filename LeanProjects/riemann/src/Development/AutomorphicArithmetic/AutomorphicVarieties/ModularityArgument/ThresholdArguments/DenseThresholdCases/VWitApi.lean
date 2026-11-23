import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.WitApi
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AAcrossOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.WeakOfAtt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.IsAutCsdA
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LevelZeroEqMaximalCompactBis
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.WeakAdmissibleIso

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory GlobalTheory.WeilDeligne GlobalTheory.CuspRep GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open private isIrr_iso from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SymmetricCubeIrreducible
namespace UpperTheory.GalN.V
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {ι : Qbar l ≃+* ℂ} {r r' : G F Ω →* GL (Fin n) (Qbar l)}
variable [IsAlgClosure F Ω]
section
variable (K : Type) [Field K] [NumberField K] [IsCMField F] [IsCMField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω]
end
theorem WitQ.weak_admissible_iso (e : RepIso r r') (h : _root_.UpperTheory.V.Z.Win.WitAQ ι r) : _root_.UpperTheory.V.Z.Win.WitAQ ι r' := by
  intro K _ _ _ _ _ _ h2 hi
  haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed F, haveI := IsAlgClosure.isAlgebraic (R := F) (K := Ω); Algebra.IsAlgebraic.tower_top (K := F) K⟩
  obtain ⟨g, hg⟩ := e
  have e' : RepIso (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω)) (r'.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω)) :=
    ⟨g, fun s => hg _⟩
  exact (h K h2 (isIrr_iso e'.symm' hi)).weak_admissible_iso e'
theorem IsAutCsdN.weak_admissible_iso [IsCMField F] (e : RepIso r r') (h0 : AutCsd0 ι r') (h : _root_.UpperTheory.V.Z.Win.IsAutCsdA ι r) :
    _root_.UpperTheory.V.Z.Win.IsAutCsdA ι r' := ⟨h0, fun c => (h.2 (continuous_of_iso c e.symm')).weak_admissible_iso e⟩
end UpperTheory.GalN.V
end
end
