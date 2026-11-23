import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsSchur
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset

theorem SchRootOfUnityVandermondeNe.rootOfUnity_isPrimitiveRoot {k : ℕ} (hk : 1 ≤ k) : IsPrimitiveRoot (rootOfUnity k) k := by
  unfold rootOfUnity
  exact Complex.isPrimitiveRoot_exp k (by omega)

theorem SchRootOfUnityVandermondeNe.proof : SchRootOfUnityVandermondeNe.Statement := by
  intro k hk
  have hz := SchRootOfUnityVandermondeNe.rootOfUnity_isPrimitiveRoot hk
  unfold vandermondeOf
  refine Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j hj => ?_
  rw [sub_ne_zero]
  intro h
  have hij : (i : ℕ) = j := hz.pow_inj i.isLt j.isLt h
  have hlt : i < j := Finset.mem_Ioi.mp hj
  exact absurd (Fin.ext hij) (ne_of_lt hlt)

end GroundTheory.Heights₂.Heights.RestTerms
