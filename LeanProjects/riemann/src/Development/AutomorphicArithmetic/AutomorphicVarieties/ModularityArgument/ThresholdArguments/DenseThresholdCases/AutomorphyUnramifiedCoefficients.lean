import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicCases.AutomorphyUnramifiedCoefficients
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.IsAutI
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.IsModular

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.U3
namespace UpperTheory.V.Aut
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
  {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ)
def AutBAlt [IsCMField K] (ι : Qbar l ≃+* ℂ) (g₁ : G ℚ Ω) : Prop :=
  ∀ (U : D.ULoc) (S : D.Ring U g₁) (ξ : entAlg c.O S.r.hom →ₐ[c.O] PadicAlgCl l)
    (r : G ℚ Ω →* GG 3 (PadicAlgCl l)) (hr : HasMult D.η r), IsPush ξ S.r.hom r → TypeI D.η r → D.IsAutIAlt ι r hr
def LemWAlt (ι : Qbar l ≃+* ℂ) (g₁ : G ℚ Ω) : Prop :=
  ∀ (U : D.ULoc) (S : D.Ring U g₁) (ξ : entAlg c.O S.r.hom →ₐ[c.O] PadicAlgCl l)
    (r : G ℚ Ω →* GG 3 (PadicAlgCl l)), IsPush ξ S.r.hom r → TypeII D.η r → (∀ g ∈ D.η.ker, (r g).mat 1 1 = 1) →
    ∀ W : G ℚ Ω →* GL (Fin 2) (PadicAlgCl l), D.IsExt r W → D.IsModularDense ι W
def AutomorphyUnramifiedCoefficientsAlt : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra K Ω]
    (l : ℕ) [Fact l.Prime] (c : Coef l) (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (D : Dat Ω K c e ψ),
    eO l c.O = 1 → ∀ ι : Qbar l ≃+* ℂ, ∃ g₁ : G ℚ Ω, D.Marked g₁ ∧ FinA D g₁ ∧ _root_.UpperTheory.V.Aut.AutBAlt D ι g₁ ∧ _root_.UpperTheory.V.Aut.LemWAlt D ι g₁
end UpperTheory.V.Aut
end
end
