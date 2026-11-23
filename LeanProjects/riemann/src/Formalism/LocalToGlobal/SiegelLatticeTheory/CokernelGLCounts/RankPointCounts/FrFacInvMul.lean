import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IotaMemO
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocOrbCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LocGlobInt
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SharpDualSpans.GlueConvA
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCount

noncomputable section

open scoped Classical Matrix

namespace Formalism.L2.SG.Pf.FibQ

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups PI.PairValDefs PI.NRCW IsDedekindDomain
  Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Key

variable {D : D7} (Z : LocDat D) (p : PlF D)

theorem cj_iota (x : D.host.E) :
    (Z.M p).L.cj ((D.s.atP p).ιE x) = (D.s.atP p).ιE (star x) := by
  rw [Z.hcj p, PI.UnitaryGroupMassFormula.CntFormula.star_eq_conjF, ← (D.s.atP p).cj_ιE]

theorem frFac_inv_mul (a : Fin (D.R.rS + 1)) : Ring.inverse (frFac Z.δ p a) * frFac Z.δ p a = 1 :=
  Ring.inverse_mul_cancel _ (Formalism.L2.SG.Pf.BBTie.bt_frFac_unit Z p a)

theorem frFac_mul_inv (a : Fin (D.R.rS + 1)) : frFac Z.δ p a * Ring.inverse (frFac Z.δ p a) = 1 :=
  Ring.mul_inverse_cancel _ (Formalism.L2.SG.Pf.BBTie.bt_frFac_unit Z p a)

theorem key_rel (N M Z₁ Z₂ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E)
    (hrel : Nᴴ * Z₂ = Z₁ * M) :
    ((locU Z p N).map (Z.M p).L.cj)ᵀ * Formalism.L2.SG.CntLocal.ZhatLoc Z.M Z.δ p Z₂ =
      Formalism.L2.SG.CntLocal.ZhatLoc Z.M Z.δ p Z₁ * locU Z p M := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, locU_apply,
    Formalism.L2.SG.CntLocal.ZhatLoc, Matrix.of_apply]
  have hL : ∀ c, (Z.M p).L.cj (Ring.inverse (frFac Z.δ p c) * (D.s.atP p).ιE (N c a) * frFac Z.δ p a) *
      (frFac Z.δ p b * (Z.M p).L.cj (frFac Z.δ p c) * (D.s.atP p).ιE (Z₂ c b)) =
      (Z.M p).L.cj (frFac Z.δ p a) * frFac Z.δ p b * (D.s.atP p).ιE (star (N c a) * Z₂ c b) := by
    intro c
    rw [map_mul, map_mul, cj_iota Z p, map_mul (D.s.atP p).ιE]
    have h1 : (Z.M p).L.cj (Ring.inverse (frFac Z.δ p c)) * (Z.M p).L.cj (frFac Z.δ p c) = 1 := by
      rw [← map_mul, frFac_inv_mul, map_one]
    calc _ = ((Z.M p).L.cj (Ring.inverse (frFac Z.δ p c)) * (Z.M p).L.cj (frFac Z.δ p c)) *
          ((Z.M p).L.cj (frFac Z.δ p a) * frFac Z.δ p b *
            ((D.s.atP p).ιE (star (N c a)) * (D.s.atP p).ιE (Z₂ c b))) := by ring
      _ = _ := by rw [h1, one_mul]
  have hR : ∀ c, frFac Z.δ p c * (Z.M p).L.cj (frFac Z.δ p a) * (D.s.atP p).ιE (Z₁ a c) *
      (Ring.inverse (frFac Z.δ p c) * (D.s.atP p).ιE (M c b) * frFac Z.δ p b) =
      (Z.M p).L.cj (frFac Z.δ p a) * frFac Z.δ p b * (D.s.atP p).ιE (Z₁ a c * M c b) := by
    intro c
    rw [map_mul (D.s.atP p).ιE]
    calc _ = (frFac Z.δ p c * Ring.inverse (frFac Z.δ p c)) *
          ((Z.M p).L.cj (frFac Z.δ p a) * frFac Z.δ p b *
            ((D.s.atP p).ιE (Z₁ a c) * (D.s.atP p).ιE (M c b))) := by ring
      _ = _ := by rw [frFac_mul_inv, one_mul]
  rw [Finset.sum_congr rfl (fun c _ => hL c), Finset.sum_congr rfl (fun c _ => hR c), ← Finset.mul_sum,
    ← Finset.mul_sum, ← map_sum, ← map_sum]
  congr 2
  have := congrFun (congrFun hrel a) b
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply] at this
  exact this

end Key

end Formalism.L2.SG.Pf.FibQ
