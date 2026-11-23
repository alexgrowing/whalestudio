import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXLeb

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def RefNBox : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u w : D.what₂.Word),
    (Measure.pi (refNX X u)) (LsNc5.boxN X w) =
      ENNReal.ofReal ((Tw w)⁻¹ ^ (D.R.rS * Fintype.card (InfinitePlace X.B.I.F)) *
        (2 : ℝ) ^ (Fintype.card (InfinitePlace X.B.I.F) * (D.R.rS * D.R.k + D.R.rS ^ 2)))

theorem refNX_haar {D : D7} (X : HidaSetting D) (u w : D.what₂.Word) :
    IsHaarOnSet X.B.I (X.NinfU w) (Measure.pi (refNX X u)) := by
  have hR := fun v : InfinitePlace X.B.I.F => refNg_isHaarLoc (nX X) (X.B.I.ε v) (eV X v) (ProductExactness.pV X v)
    (X.wfr u v) (ProductExactness.zV X u v) (ProductExactness.zV X w v) (ProductExactness.Tw_pos u) (fX_ee X v) (fX_ff X v) (fX_ef X v)
    (fX_ww X u v) (fX_ew X u v) (fX_fw X u v) (fX_ez X u v) (fX_fz X u v) (frame_real_z_z_eq_neg X u v) (fX_zw X u v) (fX_ez X w v)
  haveI : ∀ v, SigmaFinite (refNX X u v) := fun v => (hR v).1
  have hco : X.NinfU w = (ProductExactness.NinfG X w : Set X.B.I.Ginf) := (ProductExactness.NinfG_coe X w).symm
  refine ⟨inferInstance, ProductExactness.PiM.pi_ne_zero _ fun v => (hR v).2.1, ?_, ?_⟩
  · rw [hco, ProductExactness.NinfG, Subgroup.coe_pi]
    exact ProductExactness.PiM.pi_conc _ _ fun v => (hR v).2.2.1
  · intro g hg
    rw [hco] at hg
    exact ProductExactness.PiM.pi_map_mul_left _ g fun v => (hR v).2.2.2 (g v) (hg v (Set.mem_univ v))

theorem covol_refN (hN : LsNc5.CovolN) (hB : RefNBox) {D : D7} (X : HidaSetting D) (u w : D.what₂.Word)
    (FdN : Set X.B.I.Ginf) (hF : IsSFund X.B.I (Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X w) FdN) :
    ((Measure.pi (refNX X u)) FdN).toReal = |(NumberField.discr X.B.I.F : ℝ)| ^ LsNc5.covolumeExponent D.R.rS D.R.k := by
  rw [hN D X w _ FdN (refNX_haar X u w) hF, hB X u w]
  set f := Fintype.card (InfinitePlace X.B.I.F) with hf
  set r := D.R.rS with hr
  set k := D.R.k with hk
  have hT : 0 < Tw (D := D) w := ProductExactness.Tw_pos w
  have hd : 0 < |(NumberField.discr X.B.I.F : ℝ)| := abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero X.B.I.F)
  have h2r : 2 * (r * (r - 1) / 2) + 2 * (r * (r + 1) / 2) = 2 * r ^ 2 := by
    have e1 : 2 * (r * (r - 1) / 2) = r * (r - 1) := Nat.mul_div_cancel' (Nat.even_mul_pred_self r).two_dvd
    have e2 : 2 * (r * (r + 1) / 2) = r * (r + 1) := Nat.mul_div_cancel' (Nat.even_mul_succ_self r).two_dvd
    rw [e1, e2]
    rcases Nat.eq_zero_or_pos r with h0 | hpos
    · rw [h0]; simp
    · obtain ⟨m, hm⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
      rw [hm, Nat.add_sub_cancel]
      ring
  have hsum : r * (r - 1) / 2 + r * (r + 1) / 2 = r ^ 2 := by omega
  unfold LsNc5.covolN
  rw [← ENNReal.ofReal_mul (by positivity), ENNReal.toReal_ofReal (by positivity)]
  rw [show ((D.mem w).A.T : ℕ) = Tw (D := D) w from rfl]
  have hpow : (2 : ℝ) ^ (-((f * (r * k + r * (r - 1) / 2) : ℕ) : ℝ)) / (2 : ℝ) ^ (f * (r * (r + 1) / 2)) *
      (2 : ℝ) ^ (f * (r * k + r ^ 2)) = 1 := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, ← hsum]
    rw [show f * (r * k + (r * (r - 1) / 2 + r * (r + 1) / 2)) =
      f * (r * k + r * (r - 1) / 2) + f * (r * (r + 1) / 2) by ring, pow_add]
    have h1 : (0 : ℝ) < 2 ^ (f * (r * k + r * (r - 1) / 2)) := by positivity
    have h2 : (0 : ℝ) < 2 ^ (f * (r * (r + 1) / 2)) := by positivity
    field_simp
  have hTp : (Tw (D := D) w : ℝ) ^ (r * f) * (Tw (D := D) w)⁻¹ ^ (r * f) = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hT.ne', one_pow]
  calc (Tw (D := D) w : ℝ) ^ (r * f) * (2 : ℝ) ^ (-((f * (r * k + r * (r - 1) / 2) : ℕ) : ℝ)) *
        |(NumberField.discr X.B.I.F : ℝ)| ^ LsNc5.covolumeExponent r k / (2 : ℝ) ^ (f * (r * (r + 1) / 2)) *
        ((Tw (D := D) w)⁻¹ ^ (r * f) * (2 : ℝ) ^ (f * (r * k + r ^ 2)))
      = ((Tw (D := D) w : ℝ) ^ (r * f) * (Tw (D := D) w)⁻¹ ^ (r * f)) *
        ((2 : ℝ) ^ (-((f * (r * k + r * (r - 1) / 2) : ℕ) : ℝ)) / (2 : ℝ) ^ (f * (r * (r + 1) / 2)) *
          (2 : ℝ) ^ (f * (r * k + r ^ 2))) * |(NumberField.discr X.B.I.F : ℝ)| ^ LsNc5.covolumeExponent r k := by ring
    _ = |(NumberField.discr X.B.I.F : ℝ)| ^ LsNc5.covolumeExponent r k := by rw [hTp, hpow, one_mul, one_mul]

theorem covolRef_of (hN : LsNc5.CovolN) (hB : RefNBox) : CovolRef := by
  delta CovolRef
  intro D X hb FdN FdN' u u' hH
  have hd : (0 : ℝ) < |(NumberField.discr X.B.I.F : ℝ)| :=
    abs_pos.2 (Int.cast_ne_zero.2 (NumberField.discr_ne_zero _))
  rw [covol_refN hN hB X u _ FdN hH.2.2.1,
    covol_refN hN hB X u _ FdN' (by first | exact hH.2.2.2.1 | exact hH.2.2.2), ← Real.rpow_add hd]
  congr 1
  delta eDF LsNc5.covolumeExponent
  ring

theorem covolRef_of_steps (hC : LsNc5.CoordCovol) (hB : RefNBox) : CovolRef :=
  covolRef_of (covolN_of_coordCovol hC) hB

end Formalism.L2.SG.Pf.NcReal.JX
