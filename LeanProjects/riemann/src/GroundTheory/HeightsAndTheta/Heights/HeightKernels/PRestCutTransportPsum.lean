import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsRest
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem RestCutTransportPsum.proof : RestCutTransportPsum.Statement := by
  intro f j k N e m τ
  simp only [restTransport, restRename, RestTerms.blockPowerSum, rootPsum, RingHom.comp_apply,
    map_sum, map_pow, MvPolynomial.map_X, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, rename_X]
  exact Equiv.sum_comp e (fun i => (X (τ, i) : RootPoly f j k) ^ m)

end GroundTheory.Heights₂.Heights
