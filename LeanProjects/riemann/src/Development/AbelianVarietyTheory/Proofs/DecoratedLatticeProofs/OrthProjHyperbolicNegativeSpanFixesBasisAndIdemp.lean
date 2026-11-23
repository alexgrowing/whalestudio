import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagLevelCharacterEqPsiDivN
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHGamUnipKuProj
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProjectionMovesTypeVectorsModLevel
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnsCharacterEqLinkedFrameCharacter
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntAfApproxInterUnitConj
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalWIdent
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.ScalW

open Formalism.L2.SG.PoincareInHH.Cut

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem hA_eV_eV (a b : Fin D.R.rS) : hA X.B.I (eV X a) (eV X b) = 0 := by
  rw [eV, eV, HidaSetting.eR, HidaSetting.eR, hA_crd, X.ee]
  simp

theorem hA_fV_fV (a b : Fin D.R.rS) : hA X.B.I (fV X a) (fV X b) = 0 := by
  rw [fV, fV, HidaSetting.fR, HidaSetting.fR, hA_crd, X.ff]
  simp

theorem hA_eV_fV (a b : Fin D.R.rS) : hA X.B.I (eV X a) (fV X b) = if a = b then 1 else 0 := by
  rw [eV, fV, HidaSetting.eR, HidaSetting.fR, hA_crd, X.ef]
  split_ifs <;> simp

theorem hA_fV_eV (a b : Fin D.R.rS) : hA X.B.I (fV X a) (eV X b) = if b = a then 1 else 0 :=
  hA_f_e X a b

theorem hA_zV_eV (a : Fin D.R.rS) : hA X.B.I (zV X u) (eV X a) = 0 := by
  have h := (VS D).herm.eq (X.eX a) (X.zu u)
  rw [(X.zu_orth u a).1, map_zero] at h
  rw [zV, eV, HidaSetting.zR, HidaSetting.eR, hA_crd, ← h]
  simp

theorem hA_zV_fV (a : Fin D.R.rS) : hA X.B.I (zV X u) (fV X a) = 0 := by
  have h := (VS D).herm.eq (X.fY a) (X.zu u)
  rw [(X.zu_orth u a).2, map_zero] at h
  rw [zV, fV, HidaSetting.zR, HidaSetting.fR, hA_crd, ← h]
  simp

theorem hA_eV_zV (a : Fin D.R.rS) : hA X.B.I (eV X a) (zV X u) = 0 := by
  rw [zV, eV, HidaSetting.zR, HidaSetting.eR, hA_crd, (X.zu_orth u a).1]
  simp

theorem hA_fV_zV (a : Fin D.R.rS) : hA X.B.I (fV X a) (zV X u) = 0 := adelicHermitian_hyperbolicF_anisotropic_eq_zero X u a

theorem hA_zV_zV : hA X.B.I (zV X u) (zV X u) =
    -(((D.mem u).A.T : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) := by
  rw [zV, HidaSetting.zR, hA_crd, X.zu_norm]
  simp

theorem divN_zero' : divN X.B.I (D.mem u).A.T 0 = 0 := by
  simp [divN]

theorem prj_eV (b : Fin D.R.rS) : prj X u (eV X b) = eV X b := by
  simp only [prj, hA_fV_eV, hA_eV_eV, hA_zV_eV, divN_zero', ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const_zero, add_zero, sub_zero]

theorem prj_fV (b : Fin D.R.rS) : prj X u (fV X b) = fV X b := by
  simp only [prj, hA_fV_fV, hA_eV_fV, hA_zV_fV, divN_zero', ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const_zero, zero_add, sub_zero]

theorem prj_zV : prj X u (zV X u) = zV X u := by
  have hT : ((D.mem u).A.T : ℕ) ≠ 0 := (D.mem u).A.T_prime.ne_zero
  have h : divN X.B.I (D.mem u).A.T (-(((D.mem u).A.T : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) = -1 := by
    rw [show -(((D.mem u).A.T : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) =
      (((D.mem u).A.T : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (-1) by ring]
    exact Formalism.L2.SG.Pf.unitaryCongruence.divN_gmul X.B.I _ hT _
  simp only [prj, hA_fV_zV, hA_eV_zV, hA_zV_zV, h, zero_smul, Finset.sum_const_zero, zero_add,
    neg_smul, one_smul, sub_neg_eq_add]

theorem prj_prj (y : VA X.B.I) : prj X u (prj X u y) = prj X u y := by
  have hL : ∀ z, prjL X u z = prj X u z := fun _ => rfl
  rw [← hL (prj X u y)]
  conv_lhs => arg 2; rw [prj]
  simp only [map_sub, map_add, map_sum, map_smul]
  simp only [hL, prj_eV, prj_fV, prj_zV]
  rfl

theorem prj_fix_idem : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word),
    (∀ a, GlobalTheory.ScalW.prj X u (GlobalTheory.ScalW.eV X a) = GlobalTheory.ScalW.eV X a ∧
      GlobalTheory.ScalW.prj X u (GlobalTheory.ScalW.fV X a) = GlobalTheory.ScalW.fV X a) ∧
    GlobalTheory.ScalW.prj X u (GlobalTheory.ScalW.zV X u) = GlobalTheory.ScalW.zV X u ∧
    ∀ y, GlobalTheory.ScalW.prj X u (GlobalTheory.ScalW.prj X u y) = GlobalTheory.ScalW.prj X u y :=
  fun _ X u => ⟨fun a => ⟨prj_eV X u a, prj_fV X u a⟩, prj_zV X u, prj_prj X u⟩

end GlobalTheory.ScalW
