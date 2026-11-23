import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContractsOfIsoDirectSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyInvFunEquiv
open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contracts_of_iso_directSum' : ∀ (H G I F V : Type) [Monoid H] [Monoid G] [AddCommGroup F] [Module ℂ F] [AddCommGroup V] [Module ℂ V] (A B : I → Type) [∀ i, AddCommGroup (A i)] [∀ i, Module ℂ (A i)] [∀ i, AddCommGroup (B i)] [∀ i, Module ℂ (B i)] (a : ∀ i, Representation ℂ H (A i)) (b : ∀ i, Representation ℂ G (B i)) (φ : Representation ℂ (H × G) F) (σ : Representation ℂ H V) (i₀ : I), Iso (Representation.directSum fun i => Representation.tprod ((a i).comp (MonoidHom.fst H G)) ((b i).comp (MonoidHom.snd H G))) φ → (∀ i, i ≠ i₀ → invFun ((a i).tprod σ) = ⊥) → Module.finrank ℂ (invFun ((a i₀).tprod σ)) = 1 → Contracts φ σ (b i₀) := by
  first | exact @GlobalTheory.OneFunctional.contracts_of_iso_directSum | exact GlobalTheory.OneFunctional.contracts_of_iso_directSum | (intros; apply GlobalTheory.OneFunctional.contracts_of_iso_directSum <;> assumption)
