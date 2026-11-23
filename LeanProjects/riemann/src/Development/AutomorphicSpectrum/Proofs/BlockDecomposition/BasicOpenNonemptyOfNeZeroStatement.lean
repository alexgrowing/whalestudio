import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BasicOpenNonemptyOfNeZero
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeoDefs
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.basic_open_nonempty_of_ne_zero : ∀ {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N), IsIntegral X → ∀ {g : MvPolynomial (Fin (N + 1)) K} {e : ℕ}, 0 < e → ∀ (hg : g ∈ grK K N e), Ideal.Quotient.mk (homIdeal i) g ≠ 0 → ((i ⁻¹ᵁ Proj.basicOpen (grK K N) g : X.Opens) : Set X).Nonempty := by
  first | exact @GlobalTheory.CompanionTheory.Geo.preimage_basicOpen_nonempty_of_mk_ne_zero | exact GlobalTheory.CompanionTheory.Geo.preimage_basicOpen_nonempty_of_mk_ne_zero | (intros; apply GlobalTheory.CompanionTheory.Geo.preimage_basicOpen_nonempty_of_mk_ne_zero <;> assumption)
