import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt
import Development.WeilBound.CoreStatements.FlagImmersions.RestDegreePowerBound
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem kappa_bound_of_decomp : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ) (u : Wt Ψ N) (g : ℝ) (Q : Ψ → ℕ → RP Ψ N), 1 ≤ j → j < N → WeightHyp j u g → IsDecomp (linRoot u ^ (dimFl Ψ N + 1)) Q → ∀ (τ : Ψ) (σ : Ψ ⊕ Ψ) (k : ℕ), 2 ≤ k → k ≤ N → |k * degFl (pLie j (k - 1) σ * Q τ k)| ≤ ((dimFl Ψ N : ℝ) + 1) * flagDeg u * ((min j (N - j) : ℕ) * (2 ^ (k - 1) / (k.factorial : ℝ)) * ((⨆ i, u τ i) - ⨅ i, u τ i) * (N * (1 + 2 * (‖u‖ / g))) ^ (k - 1)) := by
  intro Ψ _ _ N j u g Q _ hjN hW hD τ σ k hk2 hkN
  obtain ⟨τ', I, hcard, hsmall, heq⟩ :=
    RootFieldNumerics.M5.small_block j hjN σ (k - 1) (by omega) (Q τ k)
  have hbound : ∀ i ∈ I,
      |(k : ℝ) * RootFieldNumerics.M5.alt RootFieldNumerics.M5.rho (MvPolynomial.X (τ', i) ^ (k - 1) * Q τ k)| ≤
        ((dimFl Ψ N : ℝ) + 1) * flagDeg u *
          (2 ^ (k - 1) / (k.factorial : ℝ) * ((⨆ i, u τ i) - ⨅ i, u τ i) *
            (N * (1 + 2 * (‖u‖ / g))) ^ (k - 1)) :=
    fun i hi => RootFieldNumerics.M5.one_bound j u g Q hW hD τ τ' k hk2 hkN i (hsmall i hi)
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  calc |(k : ℝ) * degFl (pLie j (k - 1) σ * Q τ k)|
      = (k : ℝ) * |RootFieldNumerics.M5.alt RootFieldNumerics.M5.rho (pLie j (k - 1) σ * Q τ k)| := by
        rw [RootFieldNumerics.M5.degFl_eq, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
          abs_of_nonneg hk0]
    _ = (k : ℝ) * |∑ i ∈ I, RootFieldNumerics.M5.alt RootFieldNumerics.M5.rho (MvPolynomial.X (τ', i) ^ (k - 1) * Q τ k)| := by
        rw [heq]
    _ = |∑ i ∈ I, (k : ℝ) * RootFieldNumerics.M5.alt RootFieldNumerics.M5.rho (MvPolynomial.X (τ', i) ^ (k - 1) * Q τ k)| := by
        rw [← Finset.mul_sum, abs_mul, abs_of_nonneg hk0]
    _ ≤ ∑ i ∈ I, |(k : ℝ) * RootFieldNumerics.M5.alt RootFieldNumerics.M5.rho (MvPolynomial.X (τ', i) ^ (k - 1) * Q τ k)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ I, ((dimFl Ψ N : ℝ) + 1) * flagDeg u *
          (2 ^ (k - 1) / (k.factorial : ℝ) * ((⨆ i, u τ i) - ⨅ i, u τ i) *
            (N * (1 + 2 * (‖u‖ / g))) ^ (k - 1)) :=
        Finset.sum_le_sum hbound
    _ = ((dimFl Ψ N : ℝ) + 1) * flagDeg u * ((min j (N - j) : ℕ) * (2 ^ (k - 1) / (k.factorial : ℝ)) *
          ((⨆ i, u τ i) - ⨅ i, u τ i) * (N * (1 + 2 * (‖u‖ / g))) ^ (k - 1)) := by
        rw [Finset.sum_const, nsmul_eq_mul, hcard]
        ring

end GlobalTheory.CompanionTheory.Ar.Top
