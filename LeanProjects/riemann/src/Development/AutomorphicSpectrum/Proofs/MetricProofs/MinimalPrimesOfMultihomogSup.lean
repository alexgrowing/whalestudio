import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FiniteMinimalPrimes
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ChPrime
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.CycDim

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.MinHom

open MvPolynomial ReciprocityTheory.AnForm.R

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem isMultiHomogIdeal_of_mem_minimalPrimes_sup :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)),
      IsMultiHomogIdeal P → IsMultiHomogIdeal D →
        ∀ Q ∈ (P ⊔ D).minimalPrimes, IsMultiHomogIdeal Q := by
  intro K _ ι _ P D hP hD Q hQ
  classical
  have toGeo : ∀ I : Ideal (MvPolynomial (Σ k, ι k) ℂ), IsMultiHomogIdeal I →
      ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomogIdeal (R := ℂ) (ι := ι) I := fun I h => h
  have hQ' : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomogIdeal (R := ℂ) (ι := ι) Q :=
    ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_isMultiHomogIdeal_of_isHomogeneous fun k =>
      ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_isHomogeneous_of_mem_minimalPrimes _
        ((ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_isHomogeneous_of_isMultiHomogIdeal (toGeo P hP) k).sup
          (ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_isHomogeneous_of_isMultiHomogIdeal (toGeo D hD) k)) hQ
  exact hQ'

end GlobalTheory.CompanionTheory.Ar.Cmp.MinHom
