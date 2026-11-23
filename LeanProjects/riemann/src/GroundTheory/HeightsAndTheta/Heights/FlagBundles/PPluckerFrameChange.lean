import Mathlib
import GroundTheory.PAdicHodge.SlopeCauchyBinet
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open Matrix Finset

theorem PluckerFrameChange.proof : PluckerFrameChange.Statement := by
  classical
  intro R _ l N V g I hI
  have hmul : (V * g).submatrix id (I.orderEmbOfFin hI) =
      V * g.submatrix id (I.orderEmbOfFin hI) := by
    ext i j; simp [Matrix.mul_apply]
  have hL : pluckerCoord (V * g) I =
      ∑ s : GroundTheory.PAdicHodge.KSubset N l,
        (V.submatrix id s.emb).det *
          ((g.submatrix id (I.orderEmbOfFin hI)).submatrix s.emb id).det := by
    rw [pluckerCoord, dif_pos hI, hmul, GroundTheory.PAdicHodge.det_mul_eq_sum_minors]
  rw [hL, Finset.sum_subtype (Finset.powersetCard l (Finset.univ : Finset (Fin N)))
    (p := fun J : Finset (Fin N) => J.card = l) (fun J => Finset.mem_powersetCard_univ)]
  refine Finset.sum_congr rfl fun s _ => ?_
  have h2 : s.1.card = l ∧ I.card = l := ⟨s.2, hI⟩
  rw [pluckerCoord, dif_pos s.2, minorOn, dif_pos h2]
  rfl

end GroundTheory.Heights₂.Heights.FlagBundles
