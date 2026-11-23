import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TeichmullerNearPowerExists
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalMod
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.teichmuller_near_power_exists : ∀ {l : ℕ} [Fact l.Prime] (S : Subring (Formalism.Per6.BdRp l)), (∀ a, wB l a ∈ S) → ∀ (ϖ : Formalism.Per6.BdRp l),
    thB l ϖ ≠ 0 → ∀ x : Tl l, ‖thB l (tch l x)‖ < 1 → ∃ M : ℕ, 0 < M ∧ Near S ϖ (FB l 1) 1 (tch l x ^ M) := by
  first | exact @GlobalTheory.CompanionTheory.LTPer.TopNil.main | exact GlobalTheory.CompanionTheory.LTPer.TopNil.main | (intros; apply GlobalTheory.CompanionTheory.LTPer.TopNil.main <;> assumption)
