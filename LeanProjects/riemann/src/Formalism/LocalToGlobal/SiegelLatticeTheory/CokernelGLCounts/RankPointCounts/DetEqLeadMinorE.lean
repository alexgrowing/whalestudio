import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CjTFromBlocks

noncomputable section

open Matrix
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal Formalism.L2.SG.Pf.PCount

namespace Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Cross

variable {D : D7}

theorem ld_eq_leadMinorE (Z : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) :
    ld Z = leadMinorE Z D.R.rS := by
  unfold ld leadMinorE
  rw [dif_pos (Nat.le_succ _)]
  rfl

theorem det_eq_leadMinorE (Z : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) :
    Z.det = leadMinorE Z (D.R.rS + 1) := by
  unfold leadMinorE
  rw [dif_pos le_rfl]
  rfl

theorem cross_global {w w' : Point D.host.E (D.R.rS + 1)} {Z Z' : PairVal.MatR D} (hk : kind w = kind w')
    (hZ : AtMat w Z) (hZ' : AtMat w' Z') : Cross Z Z' := by
  unfold Cross
  rw [ld_eq_leadMinorE, ld_eq_leadMinorE, det_eq_leadMinorE, det_eq_leadMinorE]
  exact cross_of_kind hk hZ hZ'

variable (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)

theorem cross_zhatLoc (p : PlF D) {Z Z' : MatZ D} (h : Cross Z Z') :
    Cross (ZhatLoc M δ p Z) (ZhatLoc M δ p Z') := by
  have e : ∀ Y : MatZ D, ZhatLoc M δ p Y =
      Matrix.of fun a b => frFac δ p b * (M p).L.cj (frFac δ p a) * (Y.map (D.s.atP p).ιE) a b := by
    intro Y; ext a b; simp [ZhatLoc]
  rw [e, e]
  exact cross_scale (fun a => (M p).L.cj (frFac δ p a)) (frFac δ p) (cross_map _ h)

end Cross

end Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents
