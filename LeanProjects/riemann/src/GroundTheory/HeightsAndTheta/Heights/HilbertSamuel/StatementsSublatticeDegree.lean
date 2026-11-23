import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsEuclideanSections
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

def SublatticeDegree.Statement : Prop :=
  ∀ (E E' : Type) [AddCommGroup E] [AddCommGroup E'] (R R' : ℕ) (φ : E →+ EuclideanSpace ℝ (Fin R))
    (φ' : E' →+ EuclideanSpace ℝ (Fin R')) [DiscreteTopology (imageLattice φ)] [IsZLattice ℝ (imageLattice φ)]
    [DiscreteTopology (imageLattice φ')] [IsZLattice ℝ (imageLattice φ')] (ψ : E' →+ E) (S : Set E) (C : ℝ),
    Function.Injective φ → Function.Injective φ' → Function.Injective ψ → (∀ x, ‖φ (ψ x)‖ ≤ ‖φ' x‖) →
    AddSubgroup.closure S = ⊤ → (∀ s ∈ S, ‖φ s‖ ≤ C) → 1 ≤ C →
    -Real.log (ZLattice.covolume (imageLattice φ')) ≤
      -Real.log (ZLattice.covolume (imageLattice φ)) + R * Real.log C

namespace SublatticeDegree

abbrev b1 : Module.Basis (Fin 1) ℝ (EuclideanSpace ℝ (Fin 1)) := (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis

abbrev lat1 : Submodule ℤ (EuclideanSpace ℝ (Fin 1)) := Submodule.span ℤ (Set.range b1)

abbrev φ1 : lat1 →+ EuclideanSpace ℝ (Fin 1) := lat1.subtype.toAddMonoidHom

theorem imageLattice_φ1 : imageLattice φ1 = lat1 := by
  ext x
  change x ∈ φ1.range ↔ x ∈ lat1
  rw [AddMonoidHom.mem_range]
  exact ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun h => ⟨⟨x, h⟩, rfl⟩⟩

theorem isZLattice_of_eq {L L' : Submodule ℤ (EuclideanSpace ℝ (Fin 1))} (h : L = L') [DiscreteTopology L]
    [DiscreteTopology L'] [IsZLattice ℝ L'] : IsZLattice ℝ L := by
  subst h
  assumption

instance : DiscreteTopology (imageLattice φ1) := by
  rw [imageLattice_φ1]; infer_instance

instance : IsZLattice ℝ (imageLattice φ1) := isZLattice_of_eq imageLattice_φ1

def g1 : lat1 := ⟨b1 0, Submodule.subset_span ⟨0, rfl⟩⟩

end SublatticeDegree

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
