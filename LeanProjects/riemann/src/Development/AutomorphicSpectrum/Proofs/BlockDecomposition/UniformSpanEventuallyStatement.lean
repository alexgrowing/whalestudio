import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformSpanEventually
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KerSCShortExact
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniform_span_eventually : ∀ {X : Scheme.{0}} [CompactSpace X] {k : ℕ} {K : ℕ → X.Modules} (T : Fin k → ∀ e, K e ⟶ K (e + 1)), (∀ e, (K e).IsQuasicoherent) → (∀ U : X.affineOpens, ∃ dU : ℕ, ∀ e, dU ≤ e → Submodule.span Γ(X, U) (⋃ i, Set.range ((T i e).app U)) = ⊤) → ∃ d' : ℕ, ∀ e, d' ≤ e → ∀ U : X.affineOpens, Submodule.span Γ(X, U) (⋃ i, Set.range ((T i e).app U)) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.GE.Uniform.span_range_eq_top_uniform | exact GlobalTheory.CompanionTheory.GE.Uniform.span_range_eq_top_uniform | (intros; apply GlobalTheory.CompanionTheory.GE.Uniform.span_range_eq_top_uniform <;> assumption)
