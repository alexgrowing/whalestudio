import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobXiDivPrimeUnitTendstoOne
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
open Formalism
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobXi_div_prime_unit_tendsto_one : ∀ (l : ℕ) [Fact l.Prime] (C : GlobalTheory.MemLoc.Core l), ∃ u : Per.Acris l, IsUnit u ∧ (l : Per.Acris l) * u = algebraMap (Per.Ainf l) (Per.Acris l) (Per.φA l (GlobalTheory.MemLoc.xi C.ε)) ∧ ∀ r : ℕ, ∃ M : ℕ, ∀ m ≥ M, (⇑(GlobalTheory.MemLoc.phiA l))^[m] u - 1 ∈ Ideal.span {(l : Per.Acris l)} ^ r := by
  first | exact @GlobalTheory.MemLoc.phi_xi_unit_tendsto | exact GlobalTheory.MemLoc.phi_xi_unit_tendsto | (intros; apply GlobalTheory.MemLoc.phi_xi_unit_tendsto <;> assumption)
