import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassHeight
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def GrassLinesProj.Statement : Prop :=
  ∀ (m : ℕ) (II : IntersectionSystem), IsIntersectionSystem II →
    II (Fin 1) (plBlocks 1 1 m) (grassIdeal 1 1 m) (1 * 1 * m + 1) (fun _ => fsMulti (plBlocks 1 1 m)) =
      II Unit (PBlk (m + 1)) ⊥ (m + 1) (fun _ => fsMulti (PBlk (m + 1)))

example (m : ℕ) : Fintype.card (PlIdx 1 m) = m + 1 := by
  rw [Fintype.card_subtype, ← Finset.powerset_univ, ← Finset.powersetCard_eq_filter, Finset.card_powersetCard, Finset.card_univ,
    Fintype.card_fin, Nat.choose_one_right, add_comm]

example : (Ideal (MRing (plBlocks 1 1 1)) × HermLine (plBlocks 1 1 1)) ×
    (Ideal (MRing (PBlk 2)) × HermLine (PBlk 2)) :=
  ⟨⟨grassIdeal 1 1 1, fsMulti (plBlocks 1 1 1)⟩, ⟨⊥, fsMulti (PBlk 2)⟩⟩

end

end GroundTheory.Heights₂.Heights
