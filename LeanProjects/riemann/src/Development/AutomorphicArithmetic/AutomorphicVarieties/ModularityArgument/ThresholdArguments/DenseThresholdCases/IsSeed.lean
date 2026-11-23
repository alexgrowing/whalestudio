import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.SlopeTestRemainingChoices
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.IsAutCsdA

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
namespace UpperTheory.V.Sd
section Sym
variable (R : Type) [CommRing R]
variable {Γ k : Type} [Group Γ] [Field k]
end Sym
section Cong
variable {l : ℕ} [Fact l.Prime] {Γ : Type} [Group Γ] {n : ℕ}
end Cong
section Gal
variable {Ω : Type} [Field Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
variable {F : Type} [Field F] [NumberField F] [Algebra F Ω]
variable [CharZero Ω] [IsAlgClosure ℚ Ω]
structure IsSeedAlt {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] (ι : Qbar l ≃+* ℂ) (c : G ℚ Ω)
    (ψ τ : Fin n → G L Ω →* (Qbar l)ˣ) (m : Fin n → ℤ) (ka : G L Ω →* (Qbar l)ˣ) (r : G L Ω →* GL (Fin n) (Qbar l)) : Prop where
  cont : Continuous r
  irr : IsIrr r
  pair : ∃ P : GL (Fin n) (Qbar l), (P : Matrix (Fin n) (Fin n) (Qbar l))ᵀ = P ∧ IsPair c r 1 P
  res : ResSum r ψ
  away : TypeAway r τ
  above : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → OrdAt r m ψ A
  aut : _root_.UpperTheory.V.Z.Win.IsAutCsdA ι (tw r ka)
end Gal
end UpperTheory.V.Sd
end
end
