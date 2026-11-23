import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
import Formalism.LocalToGlobal.Columns.MtHeckeSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentSumAuxiliaryPlaces
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSplitIdempotentsOfRelTraceOneModTwo
import Formalism.LocalToGlobal.Columns.RecLevelLocP
import Formalism.SatakeDualWeyl.StatementC
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg
noncomputable section

namespace GlobalTheory.IdemSupp

variable {D : D7}

def singleL (v : HeightOneSpectrum (𝓞 D.host.F)) : Fv D.host.F v →ₗ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F where
  toFun y := singleV D.host.F v y
  map_add' x y := by
    have h := GlobalTheory.IdemModTwo.singleV_sub (D := D) v (x + y) y
    rw [add_sub_cancel_right] at h
    rw [h, sub_add_cancel]
  map_smul' c y := by
    rw [RingHom.id_apply, Algebra.smul_def, Algebra.smul_def, GlobalTheory.IdemModTwo.singleV_mul (D := D), AlgHom.commutes]

theorem pl_mul_eq (v : HeightOneSpectrum (𝓞 D.host.F)) (z : Formalism.IndefR.Lev.EAf D) :
    swapAE D (finPart D (GlobalTheory.IdemModTwo.pl D v)) * z =
      TensorProduct.map (LinearMap.id : D.host.E →ₗ[D.host.F] D.host.E) (singleL (D := D) v) (Formalism.UG.prV v z) := by
  change ((1 : D.host.E) ⊗ₜ[D.host.F] singleV D.host.F v 1) * z = _
  induction z using TensorProduct.induction_on with
  | zero => rw [mul_zero, map_zero, map_zero]
  | tmul x a =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    change _ = x ⊗ₜ[D.host.F] singleV D.host.F v (evalV D.host.F v a)
    rw [mul_comm, GlobalTheory.IdemModTwo.singleV_mul (D := D), mul_one]
  | add x y hx hy => simp only [mul_add, hx, hy, map_add]

theorem idem_mul_eq_zero : ∀ {D : D7} (v : HeightOneSpectrum (𝓞 D.host.F)) (Pb : Formalism.L2.DIV.Pl D.host.E) (e : Formalism.L2.Theta.AE D), Formalism.L2.Col.IsOver v Pb → Formalism.L2.NTheta.IsIdemAt e (Formalism.L2.Col.conjPrime₂ Pb) → ∀ z : Formalism.IndefR.Lev.EAf D, Formalism.UG.prV v z = 0 → swapAE D (finPart D e) * z = 0 := by
  intro D v Pb e hov he z hz
  have hov' := Formalism.L2.Col.IsOver.conj D.sp.cm hov
  have hsp := GlobalTheory.GridIdem.splitAt_under he
  have hu : (Formalism.L2.Col.conjPrime₂ Pb).under (𝓞 D.host.F) = v := HeightOneSpectrum.ext hov'.symm
  rw [hu] at hsp
  rw [← hsp.pl_mul, map_mul, map_mul, mul_comm (swapAE D _), mul_assoc, pl_mul_eq, hz, map_zero, mul_zero]

end GlobalTheory.IdemSupp
