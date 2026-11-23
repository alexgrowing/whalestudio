import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsNumberFieldBoxCount
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open NumberField NumberField.mixedEmbedding

noncomputable def latticeImage (F : Type*) [Field F] (L : AddSubgroup F) : Submodule ℤ (mixedSpace F) :=
  (L.map (mixedEmbedding F).toAddMonoidHom).toIntSubmodule

theorem mem_latticeImage {F : Type*} [Field F] (L : AddSubgroup F) (y : mixedSpace F) :
    y ∈ latticeImage F L ↔ ∃ x ∈ L, mixedEmbedding F x = y := by
  change y ∈ L.map (mixedEmbedding F).toAddMonoidHom ↔ _
  simp

open scoped Classical in

def LatticeImageZLattice.Statement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (L : AddSubgroup F), L.FG →
    (∀ x : F, ∃ n : ℕ, 0 < n ∧ (n : F) * x ∈ L) →
      ∃ _ : DiscreteTopology (latticeImage F L), IsZLattice ℝ (E := mixedSpace F) (latticeImage F L)

end GroundTheory.Heights₂.Heights.Targets
