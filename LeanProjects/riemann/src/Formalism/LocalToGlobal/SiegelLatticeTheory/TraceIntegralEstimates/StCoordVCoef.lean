import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.ChartLaw
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StepPinExistsOfPlace
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.HermitianZZEqNeg
import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.HHRed

noncomputable section

open scoped Matrix
open Finset NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj

namespace Formalism.L2.S.Pv.Chart

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hJ_conj {n : ℕ} (ε : Fin n → Bool) (x y : Fin n → ℂ) : hJ ε x y = star (hJ ε y x) := by
  unfold hJ Formalism.REAL.Jm
  simp only [Matrix.mulVec_diagonal, dotProduct, star_sum, star_mul']
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp [mul_comm]

theorem blkOf_mono {K : Type*} : ∀ (l : List (K × ℕ)) (i j : ℕ), i ≤ j → blkOf l i ≤ blkOf l j
  | [], _, _, _ => le_rfl
  | (x, s) :: bs, i, j, h => by
    unfold blkOf
    by_cases hi : i < s
    · rw [if_pos hi]; exact Nat.zero_le _
    · have hj : ¬ j < s := fun hj => hi (lt_of_le_of_lt h hj)
      rw [if_neg hi, if_neg hj]
      exact Nat.succ_le_succ (blkOf_mono bs (i - s) (j - s) (Nat.sub_le_sub_right h s))

variable {D : D7} {w : Point D.host.E (D.R.rS + 1)}

theorem blk_mid (p : FreeE w) (c : Fin (D.R.rS + 1)) (h : p.1.1 < c ∧ c < p.1.2) :
    blkOf w.1 p.1.1.1 = blkOf w.1 c.1 ∧ blkOf w.1 c.1 = blkOf w.1 p.1.2.1 := by
  have h1 := blkOf_mono w.1 p.1.1.1 c.1 (le_of_lt h.1)
  have h2 := blkOf_mono w.1 c.1 p.1.2.1 (le_of_lt h.2)
  have h3 := p.2.2
  omega

def midL (p : FreeE w) (c : Fin (D.R.rS + 1)) (h : p.1.1 < c ∧ c < p.1.2) : FreeE w :=
  ⟨(p.1.1, c), h.1, (blk_mid p c h).1⟩

def midR (p : FreeE w) (c : Fin (D.R.rS + 1)) (h : p.1.1 < c ∧ c < p.1.2) : FreeE w :=
  ⟨(c, p.1.2), h.2, (blk_mid p c h).2⟩

def BX (p : FreeE w) (x y : FreeE w → ℂ) : ℂ :=
  ∑ c : Fin (D.R.rS + 1), if h : p.1.1 < c ∧ c < p.1.2 then x (midL p c h) * y (midR p c h) else 0

theorem BX_zero (p : FreeE w) (x : FreeE w → ℂ) : BX p x 0 = 0 := by
  unfold BX; simp

theorem BX_lower (p : FreeE w) (x x' y y' : FreeE w → ℂ)
    (h : ∀ q : FreeE w, q.1.2.val - q.1.1.val < p.1.2.val - p.1.1.val → x q = x' q ∧ y q = y' q) :
    BX p x y = BX p x' y' := by
  unfold BX
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs with hc
  · have h1 := h (midL p c hc) (by
      simp only [midL]; have := hc.1; have := hc.2
      have : c.val < p.1.2.val := hc.2
      have : p.1.1.val < c.val := hc.1
      omega)
    have h2 := h (midR p c hc) (by
      simp only [midR]
      have : c.val < p.1.2.val := hc.2
      have : p.1.1.val < c.val := hc.1
      omega)
    rw [h1.1, h2.2]
  · rfl

theorem BX_measurable (p : FreeE w) : Measurable (fun z : (FreeE w → ℂ) × (FreeE w → ℂ) => BX p z.1 z.2) := by
  unfold BX
  refine Finset.measurable_sum _ fun c _ => ?_
  split_ifs with hc
  · exact ((measurable_pi_apply _).comp measurable_fst).mul ((measurable_pi_apply _).comp measurable_snd)
  · exact measurable_const

section Law

variable (X : HidaSetting D) (v : InfinitePlace X.B.I.F)

theorem dual_v (a b : Fin D.R.rS) :
    hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) (rv X.B.I v (X.eR b)) = if a = b then 1 else 0 := by
  rw [hJ_conj, show X.eR b = X.crd (X.eX b) from rfl, show X.fR a = X.crd (X.fY a) from rfl,
    Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.hJ_rvX, X.ef]
  by_cases h : a = b
  · subst h; simp
  · rw [if_neg (Ne.symm h), if_neg h, map_zero, star_zero]

theorem fz_v (u' : D.what₂.Word) (a : Fin D.R.rS) :
    hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) (rv X.B.I v (X.zR u')) = 0 := by
  rw [show X.zR u' = X.crd (X.zu u') from rfl, show X.fR a = X.crd (X.fY a) from rfl,
    Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.hJ_rvX, (X.zu_orth u' a).2, map_zero]

theorem ha_free (q : FreeE w) : q.1.1.1 < D.R.rS := by have := q.2.1; have := q.1.2.isLt; omega

theorem stCoordV_coef (u' : D.what₂.Word) (γ : X.B.I.Ginf) (y : Formalism.REAL.UJ (X.B.I.ε v)) (q : FreeE w) :
    Formalism.L2.SG.NGPin.stCoordV X u' w γ v y q =
      (D.host.rdE : ℂ) ^ (D.R.rS - q.1.1.1) * ((D.host.rdE : ℂ) ^ (D.R.rS - q.1.2.1))⁻¹ *
        hJ (X.B.I.ε v) (rv X.B.I v (X.fR ⟨q.1.1.1, ha_free q⟩))
          (uMat ((γ v)⁻¹ * y * γ v) *ᵥ fam (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u')) q.1.2) := by
  unfold Formalism.L2.SG.NGPin.stCoordV frm famSc
  rw [Matrix.mulVec_smul, hJ_smul]
  ring

theorem stCoordV_mul {u u' : D.what₂.Word} {γ : X.B.I.Ginf} {y₁ y₂ : Formalism.REAL.UJ (X.B.I.ε v)}
    (h₁ : y₁ ∈ Formalism.L2.SG.NGPin.StV X u u' γ v) (h₂ : y₂ ∈ Formalism.L2.SG.NGPin.StV X u u' γ v) (p : FreeE w) :
    Formalism.L2.SG.NGPin.stCoordV X u' w γ v (y₁ * y₂) p =
      Formalism.L2.SG.NGPin.stCoordV X u' w γ v y₁ p + Formalism.L2.SG.NGPin.stCoordV X u' w γ v y₂ p +
        BX p (Formalism.L2.SG.NGPin.stCoordV X u' w γ v y₁) (Formalism.L2.SG.NGPin.stCoordV X u' w γ v y₂) := by
  have hdual := dual_v X v
  have hfz := fz_v X v u'
  have hS₁ : InS (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u')) (uMat ((γ v)⁻¹ * y₁ * γ v)) := h₁.2.1
  have hS₂ : InS (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u')) (uMat ((γ v)⁻¹ * y₂ * γ v)) := h₂.2.1
  have hmul : uMat ((γ v)⁻¹ * (y₁ * y₂) * γ v) = uMat ((γ v)⁻¹ * y₁ * γ v) * uMat ((γ v)⁻¹ * y₂ * γ v) := by
    rw [show (γ v)⁻¹ * (y₁ * y₂) * γ v = ((γ v)⁻¹ * y₁ * γ v) * ((γ v)⁻¹ * y₂ * γ v) by group]; rfl
  have hrd : (D.host.rdE : ℂ) ≠ 0 := by
    have := Formalism.MainNotions.S.Pv.HH.one_le_rdE D
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one this))
  have hab : (⟨p.1.1.1, ha_free p⟩ : Fin D.R.rS).1 < p.1.2.1 := p.2.1
  unfold BX
  simp only [stCoordV_coef X v u' γ]
  rw [hmul, coef_mul (X.B.I.ε v) _ _ _ hdual hfz hS₁ hS₂ ⟨p.1.1.1, ha_free p⟩ p.1.2 hab,
    Fin.sum_univ_castSucc, dif_neg (fun h => (not_lt.2 (Fin.le_last _)) h.2), add_zero]
  rw [mul_add, mul_add, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases hc : p.1.1 < c.castSucc ∧ c.castSucc < p.1.2
  · rw [dif_pos hc, if_pos ⟨hc.1, hc.2⟩]
    simp only [midL, midR]
    have e1 : fam (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u')) c.castSucc = rv X.B.I v (X.eR c) := by
      unfold fam; rw [Fin.snoc_castSucc]
    rw [e1]
    simp only [Fin.val_castSucc, Fin.eta]
    have hpow : (D.host.rdE : ℂ) ^ (D.R.rS - c.castSucc.1) ≠ 0 := pow_ne_zero _ hrd
    field_simp
  · rw [dif_neg hc, if_neg (fun h => hc ⟨h.1, h.2⟩), mul_zero]

end Law

end Formalism.L2.S.Pv.Chart

end
