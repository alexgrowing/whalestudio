import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ContinuousThetaInf

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Metric NumberField Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal Formalism.MainNotions.S Formalism.L2.SG.AdBridge
open scoped TensorProduct Matrix

def betaV {D : D7} (X : HidaSetting D) (v : InfinitePlace X.B.I.F) (Y : TupI X) :
    Matrix (Fin X.B.I.n) (Fin (D.R.rS + 1 + D.R.rS)) ℂ :=
  Matrix.of fun i b => ((X.B.I.P v)⁻¹ *ᵥ fun j => PI.AprimeInfU.thetaInf X v (Y b j)) i

theorem betaV_add {D : D7} (X : HidaSetting D) (v : InfinitePlace X.B.I.F) (Y Z : TupI X) :
    betaV X v (Y + Z) = betaV X v Y + betaV X v Z := by
  ext i b
  simp only [betaV, Matrix.of_apply, Matrix.add_apply]
  rw [← Pi.add_apply ((X.B.I.P v)⁻¹ *ᵥ _), ← Matrix.mulVec_add]
  congr 2
  funext j
  exact map_add _ _ _

theorem betaV_act {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (s : X.B.I.Ginf) (v : InfinitePlace X.B.I.F)
    (Y : TupI X) : betaV X v (X.toInf hb s • Y) = uMat (s v) * betaV X v Y := by
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  have hPu : IsUnit (X.B.I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (X.B.I.P_unit v)
  set Mm : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) :=
    ((HA.mat (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (X.toInf hb s) : GL (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) :
      Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) with hMm
  have hmap : Mm.map (PI.AprimeInfU.thetaInf X v) = X.B.I.P v * uMat (s v) * (X.B.I.P v)⁻¹ := by
    rw [uMat_toInf X hb s v, ← hMm]
    simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hPu, Matrix.one_mul]
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hPu, Matrix.mul_one]
  have hcol : ∀ b, (fun j => PI.AprimeInfU.thetaInf X v ((X.toInf hb s • Y) b j)) =
      (X.B.I.P v * uMat (s v) * (X.B.I.P v)⁻¹) *ᵥ fun j => PI.AprimeInfU.thetaInf X v (Y b j) := by
    intro b
    rw [← hmap]
    funext i
    show PI.AprimeInfU.thetaInf X v ((Mm *ᵥ Y b) i) = _
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]
  ext i b
  simp only [betaV, Matrix.of_apply, Matrix.mul_apply]
  rw [hcol b]
  rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hPu, Matrix.one_mul,
    ← Matrix.mulVec_mulVec]
  simp only [Matrix.mulVec, dotProduct]

theorem betaV_rmul {D : D7} (X : HidaSetting D) (v : InfinitePlace X.B.I.F) (a : MfI X) (Y : TupI X) :
    betaV X v (rmulT X a Y) = betaV X v Y * a.map (PI.AprimeInfU.thetaInf X v) := by
  ext i b
  simp only [betaV, Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply, rmulT, Matrix.mulVec, dotProduct,
    map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem betaV_inj {D : D7} (X : HidaSetting D) (Y Z : TupI X) (h : ∀ v, betaV X v Y = betaV X v Z) : Y = Z := by
  funext b j
  refine sub_eq_zero.1 (thetaInf_inj X _ fun v => ?_)
  have hPu : IsUnit (X.B.I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (X.B.I.P_unit v)
  have hc : (fun j => PI.AprimeInfU.thetaInf X v (Y b j)) = fun j => PI.AprimeInfU.thetaInf X v (Z b j) := by
    have e : (X.B.I.P v)⁻¹ *ᵥ (fun j => PI.AprimeInfU.thetaInf X v (Y b j)) =
        (X.B.I.P v)⁻¹ *ᵥ (fun j => PI.AprimeInfU.thetaInf X v (Z b j)) := by
      funext i
      have := congrFun (congrFun (h v) i) b
      simpa [betaV] using this
    have e2 := congrArg (fun y => X.B.I.P v *ᵥ y) e
    simpa only [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hPu, Matrix.one_mulVec] using e2
  rw [map_sub, congrFun hc j, sub_self]

end PI.AprimeInfW
