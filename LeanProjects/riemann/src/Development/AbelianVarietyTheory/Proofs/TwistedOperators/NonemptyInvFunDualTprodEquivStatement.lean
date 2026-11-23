import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyInvFunDualTprodEquiv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyInvFunEquiv
open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_invFun_dual_tprod_equiv_intertwiningMap : ∀ (G V W : Type) [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (σ : Representation ℂ G W), Nonempty (invFun (ρ.dual.tprod σ) ≃ₗ[ℂ] σ.IntertwiningMap ρ) := by
  first | exact @GlobalTheory.OneFunctional.nonempty_invFun_dual_tprod_equiv | exact GlobalTheory.OneFunctional.nonempty_invFun_dual_tprod_equiv | (intros; apply GlobalTheory.OneFunctional.nonempty_invFun_dual_tprod_equiv <;> assumption)
