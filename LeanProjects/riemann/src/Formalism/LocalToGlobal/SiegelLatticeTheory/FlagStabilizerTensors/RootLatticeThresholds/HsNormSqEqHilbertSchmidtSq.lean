import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.OOCore
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RelPtR

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.RealObj
open scoped InnerProductSpace

namespace Formalism.L2.SG.Pf.OOCoreHilbertSchmidt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hsNormSq_eq_hilbertSchmidt_sq {V V' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup V']
    [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V'] (A : V' →L[ℂ] V) :
    Formalism.MainNotions.S.hsNormSq A = Formalism.L2.SG.RealObj.hs2 A := by
  unfold Formalism.MainNotions.S.hsNormSq Formalism.MainNotions.S.hsInner Formalism.L2.SG.RealObj.hs2
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  first
    | exact inner_self_eq_norm_sq _
    | (rw [inner_self_eq_norm_sq_to_K]; norm_cast)
    | (rw [inner_self_eq_norm_sq_to_K]; simp [sq])

variable {D : D7} {X : HidaSetting D} (u u' : D.what₂.Word)

theorem hsNormSq_OOP_quot (ν : X.B.I.Ginf → Measure X.B.I.Ginf)
    (νl : Point D.host.E (D.R.rS + 1) → ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v)))
    (hQ : Formalism.L2.SG.Pf.Carrier.JointPf.OOQuot X u u' ν νl) (w : Point D.host.E (D.R.rS + 1))
    (hw : ∃ γ, IsPtRep X u u' w γ) (hG : ∀ v, 0 < GX X u u' D.host.rdE (gamW X u u' w) v) :
    Formalism.MainNotions.S.hsNormSq (Formalism.L2.SG.Pf.OOCore.OOP u u' ν w) =
      ∏ v, Formalism.MainNotions.S.hsNormSq (haveI := FiniteDimensional.complete ℂ (X.Vloc u v)
        Jv (νl w v) (X.Wloc u v) (X.Wloc u' v) ((gamW X u u' w) v)) := by
  obtain ⟨hon, hsp⟩ := Formalism.L2.SG.RealObj.EnergyCut.tens_onb X u'
  let B := OrthonormalBasis.mk hon hsp
  have hB : ∀ i, B i = X.tensU u' (fun v => stdOrthonormalBasis ℂ (X.Vloc u' v) (i v)) := fun i => by simp [B]
  have hF := hQ w hw hG
  rw [hsNormSq_eq_hilbertSchmidt_sq]
  simp only [hsNormSq_eq_hilbertSchmidt_sq]
  unfold Formalism.L2.SG.Pf.OOCore.OOP hs2
  rw [Formalism.L2.SG.RealObj.InfCut.hsb_indep (stdOrthonormalBasis ℂ (X.Vpi u')) B]
  simp only [hB, hF, Formalism.L2.SG.RealObj.RankOneTensors.norm_tens (X.tensU u) (X.tensU_inner u), ← Finset.prod_pow]
  rw [Fintype.prod_sum]

def GXPos : Prop :=
  ∀ w : Point D.host.E (D.R.rS + 1), Formalism.L2.SG.ThmBUse.IsRowPt D (D.mem u).A.T (D.mem u').A.T w →
    (∃ γ, IsPtRep X u u' w γ) → ∀ v, 0 < GX X u u' D.host.rdE (gamW X u u' w) v

variable (Y : Formalism.L2.SG.Full.Full X) {θ : ℝ} (C : Choice X θ) (hB : WuBessel C)

def LocNormP (νl : Point D.host.E (D.R.rS + 1) → ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v))) :
    Prop :=
  ∀ w : Point D.host.E (D.R.rS + 1), Formalism.L2.SG.ThmBUse.IsRowPt D (D.mem u).A.T (D.mem u').A.T w →
    (∃ g, IsPtRep X u u' w g) →
    Complex.normSq ((Formalism.L2.SG.TermOp.scl (Y.FN u) (Y.FN u') (X := X) (u := u) (u' := u') * X.volK2 : ℝ) : ℂ) *
        (∏ v, Formalism.MainNotions.S.hsNormSq (haveI := FiniteDimensional.complete ℂ (X.Vloc u v)
          Jv (νl w v) (X.Wloc u v) (X.Wloc u' v) ((gamW X u u' w) v))) *
      (Formalism.L2.SG.LoopTerm.covN (Y := Y) C u * Formalism.L2.SG.LoopTerm.covN (Y := Y) C u') =
      Formalism.L2.SG.Pf.JointAmplitudePoints.localAmplitudeProduct u u' hB w

section GX

variable {D : D7} {X : HidaSetting D}

theorem frm_sc (u : D.what₂.Word) (sc : ℝ) (v : InfinitePlace X.B.I.F) (a : Fin (D.R.rS + 1)) :
    frm X u sc v a = (((sc ^ (D.R.rS - a.val))⁻¹ : ℝ) : ℂ) • frm X u 1 v a := by
  unfold frm famSc
  simp only [Complex.ofReal_one, one_pow, inv_one, one_smul, Complex.ofReal_inv, Complex.ofReal_pow]

theorem zx_rd (u u' : D.what₂.Word) (γ : X.B.I.Ginf) (v : InfinitePlace X.B.I.F) (a b : Fin (D.R.rS + 1)) :
    ZX X u u' D.host.rdE γ v a b = ((rhoF D a * rhoF D b : ℝ) : ℂ) * ZX X u u' 1 γ v a b := by
  have hρ : ∀ c : Fin (D.R.rS + 1), rhoF D c = (D.host.rdE ^ (D.R.rS - (c : ℕ)))⁻¹ := by
    intro c
    have hc := c.isLt
    unfold rhoF
    have h1 := Real.rpow_intCast D.host.rdE (-((D.R.rS - (c : ℕ) : ℕ) : ℤ))
    rw [zpow_neg, zpow_natCast] at h1
    rw [← h1]
    congr 1
    push_cast [Nat.cast_sub (Nat.lt_succ_iff.mp hc)]
    ring
  rw [hρ a, hρ b]
  unfold ZX Formalism.L2.SG.RealObj.Zhat
  rw [frm_sc u D.host.rdE v a, frm_sc u' D.host.rdE v b, Matrix.mulVec_smul]
  unfold hJ
  simp only [Matrix.mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul,
    smul_eq_mul, Complex.star_def, Complex.conj_ofReal]
  clear hρ
  push_cast
  ring

theorem gx_eq (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (hw : ∃ γ, IsPtRep X u u' w γ)
    (τ : D.what₂.Tau) :
    GX X u u' D.host.rdE (gamW X u u' w) (vOf X τ) =
      Formalism.MainNotions.S.ThB.Gpt (Tw (D := D) u) (Tw (D := D) u') (Formalism.MainNotions.S.ThB.ptLoc D τ w) := by
  have hrep : IsPtRep X u u' w (gamW X u u' w) := by
    unfold gamW
    rw [dif_pos hw]
    exact hw.choose_spec
  have hZ : ∀ a b, ZX X u u' D.host.rdE (gamW X u u' w) (vOf X τ) a b =
      (-1 : ℂ) ^ (D.R.rS - b.val) * ptMat (Formalism.MainNotions.S.ThB.ptLoc D τ w) a b := by
    intro a b
    have h1 := congrFun (congrFun (hrep (vOf X τ)) a) b
    unfold Formalism.L2.SG.RealObj.ZhatO Formalism.L2.SG.RealObj.ptC at h1
    simp only [Matrix.map_apply] at h1
    rw [X.φ_eq, X.ιE.apply_symm_apply, show X.pl (vOf X τ) = τ from X.pl.apply_symm_apply τ] at h1
    have hs : ((-1 : ℂ) ^ (D.R.rS - b.val)) * (-1 : ℂ) ^ (D.R.rS - b.val) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]; norm_num
    rw [zx_rd, Formalism.L2.SG.Pf.RelPtR.ptMat_ptLoc τ w a b]
    have h2 : ZX X u u' 1 (gamW X u u' w) (vOf X τ) a b = (-1 : ℂ) ^ (D.R.rS - b.val) * embS D τ (ptMat w a b) := by
      rw [← h1, ← mul_assoc, hs, one_mul]
    rw [h2]
    ring
  have hD : ∀ l (hl : l ≤ D.R.rS + 1), Complex.normSq (Formalism.L2.SG.RealObj.Dl (ZX X u u' D.host.rdE (gamW X u u' w) (vOf X τ)) l) =
      Complex.normSq (leadMinor (ptMat (Formalism.MainNotions.S.ThB.ptLoc D τ w)) l hl) := by
    intro l hl
    unfold Formalism.L2.SG.RealObj.Dl leadMinor
    rw [dif_pos hl]
    have hM : (ZX X u u' D.host.rdE (gamW X u u' w) (vOf X τ)).submatrix (Fin.castLE hl) (Fin.castLE hl) =
        (ptMat (Formalism.MainNotions.S.ThB.ptLoc D τ w)).submatrix (Fin.castLE hl) (Fin.castLE hl) *
          Matrix.diagonal (fun b : Fin l => (-1 : ℂ) ^ (D.R.rS - (Fin.castLE hl b).val)) := by
      ext i j
      simp [Matrix.mul_diagonal, hZ, mul_comm]
    rw [hM, Matrix.det_mul, Matrix.det_diagonal, map_mul, map_prod]
    simp [Complex.normSq_neg]
  unfold GX Gv Formalism.MainNotions.S.ThB.Gpt
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, hD (D.R.rS + 1) le_rfl, hD D.R.rS (Nat.le_succ _)]

theorem gxPos_holds (u u' : D.what₂.Word) : GXPos (X := X) u u' := by
  intro w hb hw v
  have hv : v = vOf X (X.pl v) := (X.pl.symm_apply_apply v).symm
  rw [hv, gx_eq u u' w hw (X.pl v)]
  exact hb.2 (X.pl v)

end GX

end Formalism.L2.SG.Pf.OOCoreHilbertSchmidt
