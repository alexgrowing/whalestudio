import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedFinitenessSeparableNorm
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwFin
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_finiteness_separable_norm : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)), FiniteDimensional ℚ_[p] K → ∀ (n r : ℕ), 0 < r → ∀ δ : GL (Fin n) (KQ p K r), (nrmRes p K n r δ).val.charpoly.Separable → GlobalTheory.TwFin.TwFin (sigRes p K n r) (Kres p K n r) δ (nrmRes p K n r δ) := by
  first | (exact @GlobalTheory.TwFinGL.main) | (exact GlobalTheory.TwFinGL.main) | (intros; apply GlobalTheory.TwFinGL.main <;> assumption)
