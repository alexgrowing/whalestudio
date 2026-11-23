import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarPinVt
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CfgTopFalseIff
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierTFr
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BridgeNC
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BridgeOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierSizes
import Formalism.FormalDegreeBessel.FinalG

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped Matrix

namespace Formalism.L2.SG.Pf.Carrier.CarPinVt

open Formalism.L2.SG.RealObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

def GNonNeg (u u' : D.what₂.Word) : Prop :=
  ∀ (w : Point D.host.E (D.R.rS + 1)) (γ : X.B.I.Ginf), IsPtRep X u u' w γ → ∀ v, 0 ≤ GX X u u' D.host.rdE γ v

theorem lZero_of (u u' : D.what₂.Word) (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (FdN FdN' : Set X.B.I.Ginf) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (hG : GNonNeg X u u') :
    LZero X u u' sc i0 i0' FdN FdN' νq := by
  intro p w hp hng
  unfold VtPt
  rw [hp]
  simp only
  by_cases hrep : ∃ γ, IsPtRep X u u' w γ
  · have h1 : ¬ ∀ v, 0 < GX X u u' D.host.rdE (gamW X u u' w) v := fun h => hng ⟨hrep, h⟩
    push_neg at h1
    obtain ⟨v, hv⟩ := h1
    have hrepw : IsPtRep X u u' w (gamW X u u' w) := by
      unfold gamW; rw [dif_pos hrep]; exact hrep.choose_spec
    have h0 : GX X u u' D.host.rdE (gamW X u u' w) v = 0 := le_antisymm hv (hG w _ hrepw v)
    have hk := Formalism.MainNotions.BridgeLemma.five_le_k D
    have hn : nW X u u' w = 0 := by
      unfold nW
      refine Finset.prod_eq_zero (Finset.mem_univ v) ?_
      rw [h0, zero_pow (by omega), zero_mul]
    rw [hn, Real.sqrt_zero, Complex.ofReal_zero, zero_smul]
  · have hV : unscaledOperatorAtPointRepresentative X u u' sc i0 i0' νq w = 0 := by
      unfold unscaledOperatorAtPointRepresentative; rw [if_neg hrep]
    rw [hV, map_zero, smul_zero]

theorem gX_nonneg {θ : ℝ} (C : Formalism.L2.SG.LocWSOf.Choice X θ) (u u' : D.what₂.Word) (γ : X.B.I.Ginf)
    (v : InfinitePlace X.B.I.F) : 0 ≤ GX X u u' D.host.rdE γ v := by
  obtain ⟨hQ1, hQ2, hQ3, hQ4⟩ := Formalism.L2.SG.Pf.CarrierT.isTransp_Qcs X C v
  set Qm := Formalism.L2.SG.LocWSOf.Qcs C (X.pl v)
  set Qim := Formalism.L2.SG.LocWSOf.Qics C (X.pl v)
  set gg : ℕ := D.host.g 0 * D.host.g 1
  have hTr : Bridge.TrHyp (Formalism.L2.SG.RealObj.InfCut.PtRepPf.frU X u v) Qm Qim (fun a : Fin D.R.rS => cTor (gg : ℝ) D.R.rS a) :=
    ⟨hQ1, hQ2, hQ3, fun a => (hQ4 a a rfl).1, fun a => (hQ4 a a rfl).2⟩
  have hTr' : Bridge.TrHyp (Formalism.L2.SG.RealObj.InfCut.PtRepPf.frU X u' v) Qm Qim (fun a : Fin D.R.rS => cTor (gg : ℝ) D.R.rS a) :=
    ⟨hQ1, hQ2, hQ3, fun a => (hQ4 a a rfl).1, fun a => (hQ4 a a rfl).2⟩
  have hrd := Formalism.MainNotions.LocalModelPeriodLattices.rdE_pos D
  have hz := Formalism.L2.SG.Pf.BaseOf.zc_spec X C u v
  have hz' := Formalism.L2.SG.Pf.BaseOf.zc_spec X C u' v
  have hgv := Bridge.delta_GV hTr (Formalism.L2.SG.Pf.Carrier.uMat_unitary (γ v))
  have hG := Formalism.QuantumDeterminants.gNonneg D.R.k D.R.rS _ _ hz.1 hz'.1 (Formalism.L2.SG.Pf.BaseOf.zc_pos X C u v)
    (Formalism.L2.SG.Pf.BaseOf.zc_pos X C u' v) _ hgv
  have h1 := Bridge.zhat_cs hTr hTr' (sc := D.host.rdE) hrd.ne' (Formalism.MainNotions.S.uMat (γ v))
  set Zr := Formalism.L2.SG.RealObj.Zhat (X.B.I.ε v)
    (famSc D.host.rdE (Formalism.L2.SG.RealObj.InfCut.PtRepPf.frU X u v).e (Formalism.L2.SG.RealObj.InfCut.PtRepPf.frU X u v).z)
    (famSc D.host.rdE (Formalism.L2.SG.RealObj.InfCut.PtRepPf.frU X u' v).e (Formalism.L2.SG.RealObj.InfCut.PtRepPf.frU X u' v).z)
    (Formalism.MainNotions.S.uMat (γ v)) with hZr
  have h1' : Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS (Formalism.L2.SG.Pf.BaseOf.zc X C u v) (Formalism.L2.SG.Pf.BaseOf.zc X C u' v)
      (Qim * Formalism.MainNotions.S.uMat (γ v) * Qm) =
      Matrix.diagonal (fun a => star (Bridge.lam (fun a : Fin D.R.rS => cTor (gg : ℝ) D.R.rS a) D.host.rdE a)) * Zr *
        Matrix.diagonal (Bridge.lam (fun a : Fin D.R.rS => cTor (gg : ℝ) D.R.rS a) D.host.rdE) := h1
  unfold Formalism.QuantumDeterminants.Gf Formalism.QuantumDeterminants.Dmin at hG
  rw [hz.2, hz'.2, h1'] at hG
  have hgg0 : (0 : ℝ) < gg := by
    show (0 : ℝ) < ((D.host.g 0 * D.host.g 1 : ℕ) : ℝ)
    exact_mod_cast Nat.mul_pos (Formalism.L2.SG.Pf.CarrierSz.g_pos D).1 (Formalism.L2.SG.Pf.CarrierSz.g_pos D).2
  set κ : ℂ := -Complex.I * (((gg : ℝ) / (2 * Real.pi) : ℝ) : ℂ) with hκ
  have hc : ∀ a : Fin D.R.rS, cTor (gg : ℝ) D.R.rS a = κ ^ (D.R.rS - a.val) := by
    intro a; unfold cTor; congr 1; rw [hκ]; push_cast; field_simp
  have hκ0 : κ ≠ 0 := by
    rw [hκ]; refine mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) ?_
    exact_mod_cast (div_pos hgg0 (by positivity)).ne'
  have hlamne : ∀ a : Fin (D.R.rS + 1), Bridge.lam (fun a : Fin D.R.rS => cTor (gg : ℝ) D.R.rS a) D.host.rdE a ≠ 0 := by
    intro a h0
    have := (Bridge.cS_lam hc hrd.ne' a).1
    rw [h0, mul_zero] at this
    exact pow_ne_zero _ hκ0 this.symm
  have hlast : Bridge.lam (fun a : Fin D.R.rS => cTor (gg : ℝ) D.R.rS a) D.host.rdE (Fin.last D.R.rS) = 1 := by
    have := (Bridge.cS_lam hc hrd.ne' (Fin.last D.R.rS)).1
    have hcl : Formalism.L2.SG.Pf.CarrierTop.cS D.R.rS D.host.rdE (Fin.last D.R.rS) = 1 := by
      simp [Formalism.L2.SG.Pf.CarrierTop.cS]
    rw [hcl, one_mul] at this
    rw [this]; simp
  have hD1 : ∀ M : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ,
      (M.submatrix (Fin.castLE (Nat.le_of_lt_succ (Fin.last (D.R.rS + 1)).isLt))
        (Fin.castLE (Nat.le_of_lt_succ (Fin.last (D.R.rS + 1)).isLt))).det = RealObj.Dl M (D.R.rS + 1) :=
    fun M => by unfold RealObj.Dl; rw [dif_pos le_rfl]
  have hD2 : ∀ M : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ,
      (M.submatrix (Fin.castLE (Nat.le_of_lt_succ (⟨D.R.rS, by omega⟩ : Fin (D.R.rS + 2)).isLt))
        (Fin.castLE (Nat.le_of_lt_succ (⟨D.R.rS, by omega⟩ : Fin (D.R.rS + 2)).isLt))).det = RealObj.Dl M D.R.rS :=
    fun M => by unfold RealObj.Dl; rw [dif_pos (Nat.le_succ _)]
  rw [hD1, hD2, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hG
  have hGd := Bridge.G_diag D.R.rS Zr
    (fun a => star (Bridge.lam (fun a : Fin D.R.rS => cTor (gg : ℝ) D.R.rS a) D.host.rdE a))
    (Bridge.lam (fun a : Fin D.R.rS => cTor (gg : ℝ) D.R.rS a) D.host.rdE) (Tr D u * Tr D u') (by rw [hlast]; simp)
  rw [hGd] at hG
  have hne1 : (∏ i : Fin D.R.rS, star (Bridge.lam (fun a : Fin D.R.rS => cTor (gg : ℝ) D.R.rS a) D.host.rdE
      (Fin.castLE (Nat.le_succ D.R.rS) i))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => star_ne_zero.mpr (hlamne _)
  have hne2 : (∏ i : Fin D.R.rS, Bridge.lam (fun a : Fin D.R.rS => cTor (gg : ℝ) D.R.rS a) D.host.rdE
      (Fin.castLE (Nat.le_succ D.R.rS) i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => hlamne _
  have hpos := pow_pos (mul_pos (norm_pos_iff.mpr hne1) (norm_pos_iff.mpr hne2)) 2
  have := (mul_nonneg_iff_of_pos_left hpos).mp hG
  unfold GX Gv
  exact this

theorem lZero_of_choice {θ : ℝ} (C : Formalism.L2.SG.LocWSOf.Choice X θ) (u u' : D.what₂.Word) (sc : ℝ)
    (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (FdN FdN' : Set X.B.I.Ginf)
    (νq : X.B.I.Ginf → Measure X.B.I.Ginf) : LZero X u u' sc i0 i0' FdN FdN' νq :=
  lZero_of X u u' sc i0 i0' FdN FdN' νq fun _ γ _ v => gX_nonneg X C u u' γ v

end Formalism.L2.SG.Pf.Carrier.CarPinVt
