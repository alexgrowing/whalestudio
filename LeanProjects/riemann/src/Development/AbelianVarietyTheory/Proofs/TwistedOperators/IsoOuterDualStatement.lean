import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsoOuterDual
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyInvFunEquiv
open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iso_dual_outer_outer_dual : ∀ (ι G : Type) [Fintype ι] [Group G] (V : ι → Type) [∀ τ, AddCommGroup (V τ)] [∀ τ, Module ℂ (V τ)] [∀ τ, FiniteDimensional ℂ (V τ)] (ρ : ∀ τ, Representation ℂ G (V τ)), Iso (outer ρ).dual (outer fun τ => (ρ τ).dual) := by
  first | exact @GlobalTheory.OneFunctional.iso_outer_dual | exact GlobalTheory.OneFunctional.iso_outer_dual | (intros; apply GlobalTheory.OneFunctional.iso_outer_dual <;> assumption)
