import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.GL3.PFamily

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestA

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Classical Formalism.MainNotions

def ThMeanIn (D : D7) : Prop :=
  ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (M : IntermediateField ℚ ℂ) [NumberField M], DataIn D (tor0 D cc δ) M →
    ∀ G : (M →ₐ[ℚ] ℂ) → ℂ → ℂ, (∀ ρ, GL3Theta.IsTheta0 D.host.d (lamConj M ρ (lamOf D cc δ)) (G ρ)) →
      (∑ ρ : M →ₐ[ℚ] ℂ, Real.log (GL3Theta.normSq1 (lamConj M ρ (lamOf D cc δ)) (G ρ))) / (Module.finrank ℚ M : ℝ) ≤
        (1 / 2) * (Real.log (Real.sqrt D.host.d) - Real.eulerMascheroniConstant + logDerivativeAtOne D)

def ThetaConjugation (D : D7) : Prop :=
  ∀ (cc : Ideal (𝓞 D.host.K)), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (M : IntermediateField ℚ ℂ) [NumberField M], DataIn D (tor0 D cc δ) M → ∀ (ρ : M →ₐ[ℚ] ℂ) (t0 : ℂ),
      GL3Theta.IsTwoTorsionPointUnkilled D (lamConj M ρ (lamOf D cc δ)) t0 →
        GL3Theta.IsTheta0 D.host.d (lamConj M ρ (lamOf D cc δ)) (GL3Theta.th0 (lamConj M ρ (lamOf D cc δ)) t0)

def ConjugateTorsionPointExists (D : D7) : Prop :=
  ∀ (cc : Ideal (𝓞 D.host.K)), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (M : IntermediateField ℚ ℂ) [NumberField M], DataIn D (tor0 D cc δ) M → ∀ ρ : M →ₐ[ℚ] ℂ,
      ∃ t0, GL3Theta.IsTwoTorsionPointUnkilled D (lamConj M ρ (lamOf D cc δ)) t0

def SqrtDGammaLeLogV (D : D7) : Prop :=
  Real.log (Real.sqrt D.host.d) - Real.eulerMascheroniConstant ≤ Real.log D.host.v

def LinkMeanE : Prop :=
  ∀ D : D7, StandardLatticesGL3.useNorm D → ThMeanIn D →
    ∀ (cc : Ideal (𝓞 D.host.K)), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
      ∀ (B : Base D cc δ) (χ : IdE D → ℂ), StandardLatticesGL3.natTie D cc δ (B.eNat χ) →
        ∀ C : ℝ, 1 / 2 ≤ C → ThetaMeanBound D (tor0 D cc δ) C (B.eNat χ)

def LinkConjE : Prop :=
  ∀ D : D7, StandardLatticesGL3.useNorm D →
    ∀ (cc : Ideal (𝓞 D.host.K)), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
      ∀ (B : Base D cc δ) (χ : IdE D → ℂ), StandardLatticesGL3.natTie D cc δ (B.eNat χ) → ThetaNormConjugateIndependent D (tor0 D cc δ) (B.eNat χ)

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestA

end
