import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.FibreMultiHomog
import GroundTheory.HeightsAndTheta.Heights.Intersections.LiftZComponent
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
  GroundTheory.Heights₂.Heights.Inter.FibreMultiHomogeneous

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem FibreMultiHomog.proof : FibreMultiHomog.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' G hv hP
  classical
  refine cyc_isMultiHomogIdeal_of_isHomogeneous fun k n f hf => ?_
  rw [show (DirectSum.decompose (weightedHomogeneousSubmodule G.Φ (cycBlockWt k)) f n : MvPolynomial _ G.Φ) =
    weightedHomogeneousComponent (cycBlockWt k) n f from MvPolynomial.decompose'_apply _ _ f n]
  obtain ⟨b, hb, F, e⟩ := exists_clear G f
  rw [fibreIdeal, RingHom.mem_ker] at hf ⊢
  have hF : liftZ κ v F ∈ P' := by
    rw [← G.genericFibre_ker_target, RingHom.mem_ker, aeval_liftZ, ← e, map_mul, aeval_C]
    simp [hf]
  have hc : weightedHomogeneousComponent (cycBlockWt k.1) n (liftZ κ v F) ∈ P' := by
    have hH := cyc_isHomogeneous_of_isMultiHomogIdeal hP k.1
    have := hH n hF
    rwa [show (DirectSum.decompose (weightedHomogeneousSubmodule ℤ (cycBlockWt k.1)) (liftZ κ v F) n : MRing ι') =
      weightedHomogeneousComponent (cycBlockWt k.1) n (liftZ κ v F) from
        MvPolynomial.decompose'_apply _ _ (liftZ κ v F) n] at this
  rw [liftZ_component hv, ← G.genericFibre_ker_target, RingHom.mem_ker, aeval_liftZ, ← component_map, ← e,
    weightedHomogeneousComponent_C_mul, map_mul, aeval_C] at hc
  exact (mul_eq_zero.1 hc).resolve_left ((map_ne_zero _).2 hb)

end GroundTheory.Heights₂.Heights.Targets
