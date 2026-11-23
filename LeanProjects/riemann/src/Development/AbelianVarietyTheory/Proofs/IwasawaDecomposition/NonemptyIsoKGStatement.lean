import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyIsoKG
import Mathlib
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
open NumberField IsDedekindDomain Formalism.L2.Ker Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_isoKG_of_trace_positive : ∀ (K E : Type) [Field K] [CharZero K] [Field E] [Algebra K E] [FiniteDimensional K E] (cj : E →+* E) (σ : K →+* K) (ι : Type) [Fintype ι], Fintype.card ι = Module.finrank K E → (∀ x, cj (algebraMap K E x) = algebraMap K E (σ x)) → (∀ y, cj (cj y) = y) → (∀ y, Algebra.trace K E (cj y) = σ (Algebra.trace K E y)) → (∀ y, y ≠ 0 → ∃ a : ℚ, 0 < a ∧ Algebra.trace K E (y * cj y) = (a : K)) → Nonempty (IsoKG K E cj ι) := by
  first | exact @GlobalTheory.FourCopiesIso.nonempty_isoKG | exact GlobalTheory.FourCopiesIso.nonempty_isoKG | (intros; apply GlobalTheory.FourCopiesIso.nonempty_isoKG <;> assumption)
