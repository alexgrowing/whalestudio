import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RhoPowLowerBoundSwappedPairs
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DltEqZero
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rho_pow_lower_bound_swappedPairs : ∀ (K : UQ) (B : InvAlg K) (ι : Type) [Fintype ι] (e π : ι → B.A) (S : Finset ι) (a : K.O), B.P.Separable → K.Small a → IsFrame B e π S → ∀ k : ℕ, (k + 1) ^ (Fintype.card ι - S.card) ≤ B.rho (algebraMap K.O B.A a ^ k) := by
  first | exact @GlobalTheory.UnitLemma.Desc.rho_lower | exact GlobalTheory.UnitLemma.Desc.rho_lower | (intros; apply GlobalTheory.UnitLemma.Desc.rho_lower <;> assumption)
