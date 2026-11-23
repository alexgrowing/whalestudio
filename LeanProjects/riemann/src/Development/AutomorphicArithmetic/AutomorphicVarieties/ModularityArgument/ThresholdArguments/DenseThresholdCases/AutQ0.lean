import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.IsAutomorphicOverImagQuad
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AAcrossOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.IsAutCsdA
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.WeakOfAtt

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep UpperTheory.V.Af
namespace UpperTheory.GalN.V
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
section Conv
variable {ι : Qbar l ≃+* ℂ} {r : G F Ω →* GL (Fin n) (Qbar l)}
theorem mkCsd'_alt [IsCMField F] (h : AutCsd0 ι r) (u : Continuous r → _root_.UpperTheory.V.Z.Win.WitA ι r) : _root_.UpperTheory.V.Z.Win.IsAutCsdA ι r := ⟨h, u⟩
theorem autCsd0_of_isAutCsdA [IsCMField F] (h : _root_.UpperTheory.V.Z.Win.IsAutCsdA ι r) : AutCsd0 ι r := h.1
omit [NumberField F] in
theorem isAutomorphicOverImagQuad_of_isAutQA (h : _root_.UpperTheory.V.Z.Win.IsAutQA ι r) : IsAutomorphicOverImagQuad ι r := fun hc K _ _ _ _ _ _ h2 hi => (h hc K h2 hi).1
omit [NumberField F] in
theorem isAutQA_of_isAutomorphicOverImagQuad_of_witAQ (h : IsAutomorphicOverImagQuad ι r) (u : Continuous r → _root_.UpperTheory.V.Z.Win.WitAQ ι r) : _root_.UpperTheory.V.Z.Win.IsAutQA ι r :=
  fun hc K _ _ _ _ _ _ h2 hi => ⟨h hc K h2 hi, u hc K h2 hi⟩
end Conv
end UpperTheory.GalN.V
end
end
