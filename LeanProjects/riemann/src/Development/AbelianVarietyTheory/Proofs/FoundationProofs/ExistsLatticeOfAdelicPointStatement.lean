import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.Lt_eq_iff_inv_mul_mem_intG_and_transport : ∀ (D : D7) (N : ℕ), ∃ Lt : GA D N → Submodule (𝓞 D.host.E) (Fin N → D.host.E), (∀ g : GA D N, Moves D (g : GL (Fin N) (AE D)) (Lt g) ∧ SD D (Lt g)) ∧ Lt 1 = stdL D N ∧ (∀ g g' : GA D N, Lt g = Lt g' ↔ g⁻¹ * g' ∈ intG D N) ∧ (∀ (γA g : GA D N) γ, IsRat D (γA : GL (Fin N) (AE D)) γ → ∀ x, x ∈ Lt g ↔ γ.mulVec x ∈ Lt (γA * g)) ∧ (∀ (p : ℕ) (g : GA D N), p.Prime → TrivAt D p (g : GL (Fin N) (AE D)) → EqAt D p (stdL D N) (Lt g)) := by
  first | exact @GlobalTheory.NormSum.exists_lattice_of_adelic_point | exact GlobalTheory.NormSum.exists_lattice_of_adelic_point | (intros; apply GlobalTheory.NormSum.exists_lattice_of_adelic_point <;> assumption)
