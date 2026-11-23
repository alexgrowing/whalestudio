import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntersectionVerticalPerturbationBound
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersection_vertical_perturbation_bound : Inputs → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (D : ℕ) (L : Fin D → HermLine ι) (A B : HermLine ι) (T : Finset ℕ) (α : ℕ → ℝ), IsArithVar P (D + 1) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSmoothHerm B → (∀ p ∈ T, p.Prime ∧ 0 ≤ α p) → VertClose P T α A B → (∀ p ∈ T, ∀ j, NefAt P p (L j).a) → |II K ι P (D + 1) (Fin.snoc L A) - II K ι P (D + 1) (Fin.snoc L B)| ≤ (∑ p ∈ T, α p * Real.log p) * ptsIntegral P (pot L) fun _ => 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.lemma_v_lines | exact GlobalTheory.CompanionTheory.Ar.PB.lemma_v_lines | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.lemma_v_lines <;> assumption)
