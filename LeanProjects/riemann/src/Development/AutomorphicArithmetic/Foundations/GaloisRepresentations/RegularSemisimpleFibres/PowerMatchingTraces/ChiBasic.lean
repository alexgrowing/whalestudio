import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.MatchPowAlt

noncomputable section

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical

namespace UpperTheory.Gal.InertialTypesAlt.G

private theorem isOpen_ker_chiAt {K : Type} [Field K] [NumberField K] (n : ℕ) (χ : HChar K) (v : Pl K) :
    IsOpen {g : Gw n v | χ.loc v (Matrix.GeneralLinearGroup.det g) = 1} := by
  have h := (isOpen_ker_finIdele K (χ.1.comp (finId K)) (χ.2.1.comp (continuous_finId K))).preimage
    ((Matrix.GeneralLinearGroup.continuous_det (n := Fin n)).comp (CuspSub.continuous_locGL (a := n) v))
  convert h using 1
  ext g
  exact Iff.of_eq (congrArg (fun u => χ.1 u = 1) (finId_det_locGL v g).symm)

private theorem isLocallyConstant_chiAt {K : Type} [Field K] [NumberField K] (n : ℕ) (χ : HChar K) (v : Pl K) :
    IsLocallyConstant (chiAt n χ v) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hc : Continuous fun y : Gw n v => x⁻¹ * y := continuous_const.mul continuous_id
  have hm : (fun y : Gw n v => x⁻¹ * y) ⁻¹' {g : Gw n v | χ.loc v (Matrix.GeneralLinearGroup.det g) = 1} ∈ nhds x :=
    ((isOpen_ker_chiAt n χ v).preimage hc).mem_nhds (by simp)
  filter_upwards [hm] with y hy
  have hy' : χ.loc v (Matrix.GeneralLinearGroup.det (x⁻¹ * y)) = 1 := hy
  rw [map_mul, map_mul, map_inv, map_inv] at hy'
  have e : χ.loc v (Matrix.GeneralLinearGroup.det y) = χ.loc v (Matrix.GeneralLinearGroup.det x) :=
    (inv_mul_eq_one.1 hy').symm
  simp only [chiAt, e]

theorem chiBasic : ChiBasic := by
  intro K _ _ n χ v
  refine ⟨isLocallyConstant_chiAt n χ v, fun g => ?_, fun f hf => ?_⟩
  · simp only [chiAt, HChar.loc_inv]
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  · exact ⟨hf.1.mul (isLocallyConstant_chiAt n χ v), hf.2.mul_right⟩

end UpperTheory.Gal.InertialTypesAlt.G
