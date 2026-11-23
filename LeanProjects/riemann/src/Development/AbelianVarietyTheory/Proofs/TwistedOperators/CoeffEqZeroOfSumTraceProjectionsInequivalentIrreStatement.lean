import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoeffEqZeroOfSumTraceProjectionsInequivalentIrre
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ExponentSeparation
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_eq_zero_of_sum_trace_projections_inequivalent_irreps : ∀ (G : Type) [Group G] (n : ℕ) (W : Fin n → Type) [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)] (σ : ∀ i, Representation ℂ G (W i)), (∀ i, (σ i).IsIrreducible) → (∀ i j, i ≠ j → IsEmpty ((σ i).Equiv (σ j))) → ∀ (P : ∀ i, W i →ₗ[ℂ] W i), (∀ i, P i ∘ₗ P i = P i) → (∀ i, FiniteDimensional ℂ (LinearMap.range (P i))) → ∀ a : Fin n → ℂ, (∀ (g : G) (c : Fin n → ℂ), (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasFinTrace (P i ∘ₗ σ i g ∘ₗ P i) (c i)) → ∑ i, a i * c i = 0) → ∀ i, P i ≠ 0 → a i = 0 := by
  first | exact @GlobalTheory.TraceSep.coeff_eq_zero_of_sum_trace_eq_zero | exact GlobalTheory.TraceSep.coeff_eq_zero_of_sum_trace_eq_zero | (intros; apply GlobalTheory.TraceSep.coeff_eq_zero_of_sum_trace_eq_zero <;> assumption)
