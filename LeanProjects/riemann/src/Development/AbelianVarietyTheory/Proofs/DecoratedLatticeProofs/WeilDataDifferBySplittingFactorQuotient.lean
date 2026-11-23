import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumTwistHeckeCharacters
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumUniqueOnThetaFunctions
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TopFormula
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SplitLastBlockActX
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker

namespace GlobalTheory.WeilChange

theorem weilData_differ_by_splitFac : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT χS' χT' : (AE D)ˣ →* Circle) (om om' : Om S T), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S T χS' χT' om' → ∀ g h x y, IsDetRoot S g x → IsDetRoot T h y → ∀ f, IsThetaFunO ψ S T f → om' (g, h) f = ((splitFacO χS' χT' x y : ℂ) * (splitFacO χS χT x y : ℂ)⁻¹) • om (g, h) f := by
  intro D ψ S T χS χT χS' χT' om om' H H' g h x y hx hy f hf
  have rS : ResEta D (χS⁻¹ * χS') 0 :=
    resEta_parity (resEta_mul (resEta_inv H.resS) H'.resS) (by omega)
  have rT : ResEta D (χT⁻¹ * χT') 0 :=
    resEta_parity (resEta_mul (resEta_inv H.resT) H'.resT) (by omega)
  obtain ⟨om₂, H₂, h₂⟩ := exists_weilDatum_twist D ψ H.std S T χS χT (χS⁻¹ * χS') (χT⁻¹ * χT') om H
    (hecke_mul (hecke_inv H.hecS) H'.hecS) (hecke_mul (hecke_inv H.hecT) H'.hecT) rS rT
  rw [mul_inv_cancel_left, mul_inv_cancel_left] at H₂
  rw [GlobalTheory.WeilUniq.weilDatum_unique D ψ H.std S T χS' χT' om' om₂ H' H₂ (g, h) f hf, h₂ g h x y hx hy, LinearMap.smul_apply]
  congr 1
  rw [← Circle.coe_inv, ← Circle.coe_mul]
  congr 1
  simp only [splitFacO, MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv, inv_inv]
  generalize (χT' x)⁻¹ = a, (χS y)⁻¹ = b, χS' y = c, χT x = d
  apply Circle.ext
  simp only [Circle.coe_mul]
  ring

end GlobalTheory.WeilChange
