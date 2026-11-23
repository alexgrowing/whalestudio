import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LubinTateScaledIterateTends
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalMod
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lubin_tate_scaled_iterate_tends : ∀ {B : Type} [CommRing B] {S : Subring B} {F : ℕ → Ideal B} {ϖ : B}, PerEnv S F ϖ → ∀ (ϖ' : B), ϖ * ϖ' = 1 → ∀ (q : ℕ), 2 ≤ q →
    ∀ Q ∈ S, (∃ M : ℕ, 0 < M ∧ Near S ϖ (F 1) 1 (Q ^ M)) →
      ∃ t, Tends S F ϖ (fun n => ϖ' ^ n * ltIter ϖ q n Q) t := by
  first | exact @GlobalTheory.CompanionTheory.LTPer.LogConv.log_converges | exact GlobalTheory.CompanionTheory.LTPer.LogConv.log_converges | (intros; apply GlobalTheory.CompanionTheory.LTPer.LogConv.log_converges <;> assumption)
