import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomogeneousIntegralExpression
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeoDefs
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homogeneous_integral_expression : ∀ {K σ : Type} [Field K] {m : ℕ} (I : Ideal (MvPolynomial σ K)), (∀ f ∈ I, ∀ n : ℕ, MvPolynomial.homogeneousComponent n f ∈ I) → ∀ (e : ℕ), 0 < e → ∀ (y : Fin m → MvPolynomial σ K), (∀ k, (y k).IsHomogeneous e) → Module.Finite (Algebra.adjoin K (Set.range fun k => Ideal.Quotient.mk I (y k))) (MvPolynomial σ K ⧸ I) → ∀ (w : ℕ) (a : MvPolynomial σ K), a.IsHomogeneous (e * w) → ∃ (s : ℕ) (c : ℕ → MvPolynomial (Fin m) K), 0 < s ∧ (∀ l, (c l).IsHomogeneous ((s - l) * w)) ∧ a ^ s + ∑ l ∈ Finset.range s, MvPolynomial.aeval y (c l) * a ^ l ∈ I := by
  first | exact @GlobalTheory.CompanionTheory.Geo.exists_hom_relation | exact GlobalTheory.CompanionTheory.Geo.exists_hom_relation | (intros; apply GlobalTheory.CompanionTheory.Geo.exists_hom_relation <;> assumption)
