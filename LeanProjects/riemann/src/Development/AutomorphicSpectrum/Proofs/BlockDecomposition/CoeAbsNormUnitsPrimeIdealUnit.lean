import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
import GroundTheory.AutomorphicForms.GL2.GJMatrixLocal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneDim

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar adeleAt glAt restrictedTensor2 vecAt awayIntegral awayBox)
open GroundTheory.Automorphic.GJMatrix (cosetInd localTensor localFourierPi localMeasurePi)
open Ad3 Ad3.R
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap nonZeroDivisors Classical

namespace GlobalTheory.CompanionTheory.RSFT

def absNormUnits : (FractionalIdeal (𝓞 ℚ)⁰ ℚ)ˣ →* ℝˣ :=
  Units.map (((Rat.castHom ℝ : ℚ →+* ℝ) : ℚ →* ℝ).comp
    (FractionalIdeal.absNorm : FractionalIdeal (𝓞 ℚ)⁰ ℚ →*₀ ℚ).toMonoidHom)

theorem coe_absNormUnits (I : (FractionalIdeal (𝓞 ℚ)⁰ ℚ)ˣ) :
    ((absNormUnits I : ℝˣ) : ℝ) =
      ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 ℚ)⁰ ℚ) : ℚ) : ℝ) := rfl

theorem coe_absNormUnits_primeIdealUnit (w : Pl) :
    ((absNormUnits (primeIdealUnit w) : ℝˣ) : ℝ) = (pOf w : ℝ) := by
  rw [coe_absNormUnits, coe_primeIdealUnit, FractionalIdeal.coeIdeal_absNorm]
  simp [pOf]

theorem idl_eq_prod (S : Finset Pl) (N : S → ℤ) :
    idl S N = ∏ v : S, primeIdealUnit v.1 ^ N v := by
  have hsub : Function.mulSupport (fun w : Pl =>
      primeIdealUnit w ^ (if h : w ∈ S then N ⟨w, h⟩ else 0)) ⊆ (S : Set Pl) := by
    intro w hw
    by_contra h
    apply hw
    have h' : w ∉ S := h
    simp [h']
  rw [idl, finprod_eq_prod_of_mulSupport_subset _ hsub, ← Finset.prod_coe_sort S]
  refine Finset.prod_congr rfl fun v _ => ?_
  simp

theorem absNorm_idl (S : Finset Pl) (N : S → ℤ) :
    ((FractionalIdeal.absNorm ((idl S N : (FractionalIdeal (𝓞 ℚ)⁰ ℚ)ˣ) :
      FractionalIdeal (𝓞 ℚ)⁰ ℚ) : ℚ) : ℝ) = ∏ v : S, (pOf v.1 : ℝ) ^ N v := by
  rw [← coe_absNormUnits, idl_eq_prod, map_prod, Units.coe_prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [map_zpow, Units.val_zpow_eq_zpow_val, coe_absNormUnits_primeIdealUnit]

theorem finiteAdeleMeasure_idl_toReal (S : Finset Pl) (N : S → ℤ) :
    (finiteAdeleMeasure ℚ (idealFiniteAdeles (idl S N))).toReal =
      ∏ v : S, (pOf v.1 : ℝ) ^ (-N v) := by
  rw [finiteAdeleMeasure_idealFiniteAdeles_toReal, Rat.numberField_discr]
  have hd : (NNReal.sqrt ‖(1 : ℤ)‖₊ : ℝ) = 1 := by simp
  rw [hd, inv_one, mul_one]
  have hn := absNorm_idl S N
  rw [show ((FractionalIdeal.absNorm ((idl S N : (FractionalIdeal (𝓞 ℚ)⁰ ℚ)ˣ) :
      FractionalIdeal (𝓞 ℚ)⁰ ℚ) : ℝ)) = _ from hn, ← Finset.prod_inv_distrib]
  exact Finset.prod_congr rfl fun v _ => (_root_.zpow_neg _ _).symm

end GlobalTheory.CompanionTheory.RSFT

end
