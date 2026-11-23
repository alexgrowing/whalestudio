import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.LocalizeNefAboveSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.LocalizeSubvarSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.LocalizeRestrLenSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.BaseChangeTwist
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial Kleiman

theorem LocalizeNefAbove.proof (h₁ : LocalizeSubvar.Statement) (h₂ : LocalizeRestrLen.Statement) :
    LocalizeNefAbove.Statement := by
  intro S _ 𝔪 _ O _ _ _ Ω _ _ _ _ N x M hM pp' hJ hpp'
  have hJp : 𝔪.map (C : S →+* Poly S N) ≤
      pp'.comap (MvPolynomial.map (algebraMap S O) : Poly S N →+* Poly O N) := by
    rw [Ideal.map_le_iff_le_comap]
    intro m hm
    change MvPolynomial.map (algebraMap S O) (C m) ∈ pp'
    rw [map_C]
    exact hJ (Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hm))
  have hL : (![M.baseChange O] : Fin 1 → SubSystem O x Ω) = fun i => (![M] i).baseChange O := by
    funext i; fin_cases i; rfl
  have key : interNum pp' ![M.baseChange O] =
      interNum (pp'.comap (MvPolynomial.map (algebraMap S O) : Poly S N →+* Poly O N)) ![M] := by
    unfold interNum
    congr 1
    funext c
    unfold interSum
    refine Finset.sum_congr rfl fun T _ => ?_
    congr 1
    rw [hL, baseChange_tensorSub, ← baseChange_twistSys (S := S), ← baseChange_twist]
    exact h₂ S 𝔪 O Ω N x pp' hJ _
  rw [key]
  exact hM _ hJp (h₁ S 𝔪 O Ω N x pp' 1 hJ hpp')

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
