import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelOperatorsEventuallyGenerate
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KerOpsComm
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_operators_eventually_generate : GlobalTheory.CompanionTheory.GE.GradedNoeth → ∀ {X : AlgebraicGeometry.Scheme.{0}} [AlgebraicGeometry.IsLocallyNoetherian X] {k : ℕ} {M : ℕ → X.Modules} {T : Fin (k + 1) → ∀ e, M e ⟶ M (e + 1)} {d : ℕ} (hM : GlobalTheory.CompanionTheory.GE.OpSeq (k + 1) M T d) (U : X.affineOpens), ∃ d₁ : ℕ, ∀ e, d₁ ≤ e → Submodule.span Γ(X, U) (⋃ i, Set.range ((GlobalTheory.CompanionTheory.GE.UV.kerOps hM.comm i e).app U)) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.GE.UV.kerOps_gen_bounded | exact GlobalTheory.CompanionTheory.GE.UV.kerOps_gen_bounded | (intros; apply GlobalTheory.CompanionTheory.GE.UV.kerOps_gen_bounded <;> assumption)
