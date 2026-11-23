import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.ExistsLeftInvOfIndep
import Formalism.LocalToGlobal.GlobalTheory.VolumeCarry.VolumeTheoremTwoOfRationalFrames
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GEqBase
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GrowthMod

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Eqv MeasureTheory
  IsDedekindDomain NumberField

namespace Formalism.IndefR.Mi

set_option synthInstance.maxHeartbeats 400000

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {A T : HSp D} {ι : A.V →ₗ[D.host.E] T.V}

theorem frameMat_eq_global : frameMat T A ι = Formalism.L2.GlobalTheoryTheory.VolumeCarry.frameMat D T A ι := by
  ext i j
  simp [frameMat, Formalism.L2.GlobalTheoryTheory.VolumeCarry.frameMat, LinearMap.toMatrix_apply]

def embP' (A T : HSp D) (ι : A.V →ₗ[D.host.E] T.V) : Matrix (Fin A.rank) (Fin T.rank) D.host.E :=
  A.gram⁻¹ * Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat T A ι) * T.gram

theorem embP'_mul (hι : HSpace.IsIsomEmb A T ι) : embP' A T ι * frameMat T A ι = 1 := by
  have hG := Formalism.L2.GlobalTheoryTheory.VolumeCarry.gram_frameMat D T A ι hι
  rw [← frameMat_eq_global] at hG
  unfold embP'
  rw [show A.gram⁻¹ * Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat T A ι) * T.gram * frameMat T A ι =
      A.gram⁻¹ * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat T A ι) * T.gram * frameMat T A ι) by
      simp only [Matrix.mul_assoc], ← hG]
  exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (Formalism.IndefR.Eqv.gram_det_ne' D A))

theorem perp_of_embP' (hι : HSpace.IsIsomEmb A T ι) :
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat T A ι) * T.gram * (1 - frameMat T A ι * embP' A T ι) = 0 := by
  have hG := Formalism.L2.GlobalTheoryTheory.VolumeCarry.gram_frameMat D T A ι hι
  rw [← frameMat_eq_global] at hG
  have hu : A.gram * A.gram⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (Formalism.IndefR.Eqv.gram_det_ne' D A))
  rw [Matrix.mul_sub, Matrix.mul_one]
  unfold embP'
  rw [sub_eq_zero]
  calc Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat T A ι) * T.gram
      = A.gram * A.gram⁻¹ * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat T A ι) * T.gram) := by
        rw [hu, Matrix.one_mul]
    _ = _ := by rw [hG]; simp only [Matrix.mul_assoc]

set_option maxHeartbeats 1000000 in

theorem mt_of_embRel (hι : HSpace.IsIsomEmb A T ι) {g : GA D T} {h : GA D A} (hr : EmbRel T A ι g h) :
    mt T g = (frameMat T A ι).map (incA D) * mt A h * (embP' A T ι).map (incA D) +
      (1 - (frameMat T A ι * embP' A T ι).map (incA D)) := by
  set F := frameMat T A ι
  set P := embP' A T ι
  set Q : Matrix (Fin T.rank) (Fin T.rank) D.host.E := 1 - F * P with hQ
  have hperp : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) F * T.gram * Q = 0 := perp_of_embP' hι
  have h1 : mt T g * F.map (incA D) = F.map (incA D) * mt A h := hr.1
  have h2 : mt T g * Q.map (incA D) = Q.map (incA D) := by
    ext i k
    have hx : (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) F * T.gram).mulVec (fun i => Q i k) = 0 := by
      funext i'
      have := congrFun (congrFun hperp i') k
      rw [Matrix.mul_apply, Matrix.zero_apply] at this
      rw [Pi.zero_apply, Matrix.mulVec, dotProduct]
      exact this
    have := congrFun (hr.2 (fun i => Q i k) hx) i
    rw [Matrix.mulVec, dotProduct] at this
    rw [Matrix.mul_apply, Matrix.map_apply]
    exact this
  have hQmap : Q.map (incA D) = 1 - (F * P).map (incA D) := by
    ext i j
    simp only [hQ, Matrix.map_apply, Matrix.sub_apply, map_sub, Matrix.one_apply]
    split_ifs <;> simp
  have hsplit : (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)) = (F * P).map (incA D) + Q.map (incA D) := by
    rw [hQmap, add_sub_cancel]
  calc mt T g = mt T g * 1 := (Matrix.mul_one _).symm
    _ = mt T g * (F.map (incA D) * P.map (incA D)) + mt T g * Q.map (incA D) := by
        rw [hsplit, Matrix.mul_add, Matrix.map_mul]
    _ = _ := by rw [← Matrix.mul_assoc, h1, h2, hQmap]

end Formalism.IndefR.Mi

end
