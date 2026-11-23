import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.TsgPolyVolPolyCoeffEven
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HeightPolynomialReflectionSumStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.KillNoneFormPoly
import Development.AutomorphicSpectrum.Proofs.MetricProofs.EtaleAwayOfIsEtaleAtOffSubmonoid
import GroundTheory.HeightsAndTheta.Heights.Intersections.PFibreLocal
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem thmA_swap : Inputs → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N d : ℕ) (S : AnSys (d + 1) (Ψ × Fin N)) (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (Re : Realis S P) (τ : Ψ) (a b : Fin N), (b : ℕ) = a + 1 → SqSys Re (τ, a) (xiCoef τ a) → ∀ lam : Ψ × Fin N → ℝ, eval lam (toWt (Re.PB II)) + eval (lam ∘ Equiv.swap (τ, a) (τ, b)) (toWt (Re.PB II)) = (tsgPoly (d + 1) kappa (linePoly (fun p => gap lam p + gap lam (τ, a) / 2 * (xiCoef τ a p : ℝ)) (xiCoef τ a) S.degPoly)).eval (gap lam (τ, a)) := by
  intro hI II hII Ψ _ _ N d S K _ ι _ P Re τ a b hb Q lam
  obtain ⟨h0, h1, h2⟩ := gap_swap_decomp Ψ N τ a b hb lam
  have key := GlobalTheory.T.height_polynomial_reflection_sum hI GroundTheory.Heights₂.Heights.Inter.FibreLocal.proof II hII K ι d (Ψ × Fin N) S P Re (τ, a) (xiCoef τ a) Q
    (fun p => gap lam p + gap lam (τ, a) / 2 * (xiCoef τ a p : ℝ)) h0 (gap lam (τ, a))
  rw [eval_toWt_gap, eval_toWt_gap, ← key]
  exact congrArg₂ (· + ·) (congrArg (fun f => eval f (Re.PB II)) (_root_.funext h1))
    (congrArg (fun f => eval f (Re.PB II)) (_root_.funext h2))

end GlobalTheory.CompanionTheory.Ar.PB
