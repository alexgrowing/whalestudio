import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HomogeneousLocalization.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

universe u

noncomputable section

namespace SectionsLatticeFS

open ProjScheme

theorem FSValue.proof (h : FSCoord.Statement.{u}) : FSValue.Statement.{u} := by
  intro A _ N n ρ P hP x
  have hj := rep_chartIndex_ne_zero x.1
  have hc := h A N n ρ P hP x (CP.chartIndex x.1) hj
  have hcoord : fsFrameCoord n ρ x ((self A N).evalGlobalSection (twistN A N n) x (polySection hP)) =
      evalAt ρ x.1.rep P / x.1.rep (CP.chartIndex x.1) ^ n :=
    eq_div_of_mul_eq (pow_ne_zero _ hj) hc
  have hpos : 0 < ‖x.1.rep (CP.chartIndex x.1)‖ ^ n := pow_pos (norm_pos_iff.mpr hj) n
  rw [fsFibreNorm, hcoord, CP.fsNormPoly, MvPolynomial.eval_map, norm_div, norm_pow,
    div_mul_cancel₀ _ hpos.ne']

end SectionsLatticeFS

end

end GroundTheory.Heights₂.Heights
