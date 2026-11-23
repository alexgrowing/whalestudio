import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TCoefMInMMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PencilOptionEquivLeftRenameSome
open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A

namespace GlobalTheory

theorem coefM_pencil : GlobalTheory.PsCo.Cw2a.T_coefM_pencil := by
  intro n L I _ _ A0 B0
  have h := pencil_det_adjugate_coeff (τ := Fin L ⊕ EntIdx n) A0 B0
  simpa only [coefM, muM, inM, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    Polynomial.lcoeff_apply, AlgEquiv.toLinearMap_apply, AlgHom.coe_coe] using h

end GlobalTheory
