import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.PlacesOverFinite.LinkedEndEOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PrDesc

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Sd
namespace UpperTheory.V.Z.Sym.Pl
def LinkedEndEAlt : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : Coef l)
    [CharP (ResidueField c.O) l] (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N), 1 ≤ e → Even N →
  ∀ (η : G ℚ Ω →* ℤˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ), l * N ∣ M →
    (∀ B' : ValuationSubring Ω, ¬ Ine (F := ℚ) B' ≤ η.ker → B'.valuation (M : Ω) < 1) →
  ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] (Φ : Fr.Frame l (ResidueField c.O)) (C₀ : ℕ)
    (k : Pr.GalLink η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B M L Φ), B.valuation (l : Ω) < 1 → Φ.Ok C₀ → Φ.Big C₀ →
    Pr.SeedClause c η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ L →
    Pr.FinPt c.O Φ 3 ∧ _root_.UpperTheory.V.Pr.AutPtAlt k 3 ι (cycBar L Ω l)⁻¹ ∧ ∃ ka, Sd.IsAlgChar ι ka ∧ _root_.UpperTheory.V.Pr.AutPtAlt k 2 ι ka
end UpperTheory.V.Z.Sym.Pl
end
end
