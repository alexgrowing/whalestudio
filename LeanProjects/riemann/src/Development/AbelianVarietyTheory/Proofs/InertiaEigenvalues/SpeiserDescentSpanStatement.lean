import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpeiserDescentSpan
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_span_fixed_of_semilinear_action : ∀ {G L Ω M : Type} [Group G] [Field L] [Field Ω] [Algebra L Ω] [AddCommGroup M] [Module Ω M] [Module L M] [IsScalarTower L Ω M] (b : G → Ω → Ω) (a : G → L →+* Ω) (σ : G → M →+ M) (W : Submodule L M), (∀ g h c, a (g * h) c = b g (a h c)) → (∀ c, a 1 c = algebraMap L Ω c) → (∀ m, σ 1 m = m) → (∀ g h m, σ (g * h) m = σ g (σ h m)) → (∀ g (c : L) m, σ g (c • m) = a g c • σ g m) → (Set.range a).Finite → (∀ g, ∀ m ∈ W, σ g m ∈ W) → (∀ g, (∀ c, a g c = algebraMap L Ω c) → ∀ m ∈ W, σ g m = m) → ∀ m ∈ W, m ∈ Submodule.span Ω {m | m ∈ W ∧ ∀ g, σ g m = m} := by
  first | exact @GlobalTheory.speiser_descent_span | exact GlobalTheory.speiser_descent_span | (intros; apply GlobalTheory.speiser_descent_span <;> assumption)
