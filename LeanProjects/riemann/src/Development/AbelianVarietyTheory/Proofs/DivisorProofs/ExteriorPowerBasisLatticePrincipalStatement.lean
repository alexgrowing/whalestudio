import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExteriorPowerBasisLatticePrincipal
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exteriorPower_basis_lattice_principal : ∀ (C : Type) [Field C] (O : Type) [CommRing O] [Algebra O C] (V : Type) [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V] (N : ℕ) (b : Module.Basis (Fin N) C V), Module.finrank C (⋀[C]^N V) = 1 ∧ exteriorPower.ιMulti C N b ≠ 0 ∧ Submodule.span O {w : ⋀[C]^N V | ∃ x : Fin N → V, (∀ i, x i ∈ (Submodule.span O (Set.range b) : Set V)) ∧ w = exteriorPower.ιMulti C N x} = Submodule.span O {exteriorPower.ιMulti C N b} := by
  first | exact @GlobalTheory.span_wedge_of_span_basis | exact GlobalTheory.span_wedge_of_span_basis | (intros; apply GlobalTheory.span_wedge_of_span_basis <;> assumption)
