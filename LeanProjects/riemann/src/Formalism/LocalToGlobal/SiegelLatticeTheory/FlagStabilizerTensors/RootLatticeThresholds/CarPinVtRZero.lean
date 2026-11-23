import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarPinVt
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierTIn
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BridgeOrbVec
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierSizes

noncomputable section

open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.Carrier.CarPinVt

open Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.Pf.Built Formalism.L2.SG.LocWSOf
  Formalism.L2.SG.Pf.CarrierT

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem exists_nonneg_ptG_lptOf_eq_mul (v : InfinitePlace X.B.I.F) (κ : ℂ) (hκ : star κ = -κ) (TT : ℝ)
    (w : Point D.host.E (D.R.rS + 1)) :
    ∃ c : ℝ, 0 ≤ c ∧ Formalism.FourierDecayAlt.D.ptG TT D.R.rS (Bridge.lptOf ((X.B.I.φ v).comp X.ιE.symm.toRingHom) κ D.R.rS 0 w.1) =
      c * (‖RealObj.Dl (RealObj.ZhatO (ptC X v w)) (D.R.rS + 1)‖ ^ 2 -
        TT * ‖RealObj.Dl (RealObj.ZhatO (ptC X v w)) D.R.rS‖ ^ 2) := by
  set σ : D.host.E →+* ℂ := (X.B.I.φ v).comp X.ιE.symm.toRingHom
  set Y := RealObj.ZhatO (ptC X v w)
  have hY : ptC X v w = Matrix.diagonal (fun _ => 1) * Y * Matrix.diagonal (Formalism.L2.SG.Pf.CarrierTop.sgnV D.R.rS) := by
    rw [← Formalism.L2.SG.Pf.CarrierTop.zhatO_eq_mul, Formalism.L2.SG.Pf.CarrierTop.zhatO_invol]
  have hM : Formalism.FourierDecayAlt.D.ptMatN (Bridge.lptOf σ κ D.R.rS 0 w.1) (D.R.rS + 1) =
      Matrix.diagonal (fun a : Fin (D.R.rS + 1) => Bridge.Af κ D.R.rS a * 1) * Y *
        Matrix.diagonal (fun b : Fin (D.R.rS + 1) => Formalism.L2.SG.Pf.CarrierTop.sgnV D.R.rS b * Bridge.Bf κ D.R.rS b) := by
    rw [Bridge.ptMatN_lptOf σ κ D.R.rS hκ w]
    show Matrix.diagonal _ * ptC X v w * Matrix.diagonal _ = _
    rw [hY]
    ext a b
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
    ring
  have hdet1 : (Formalism.FourierDecayAlt.D.ptMatN (Bridge.lptOf σ κ D.R.rS 0 w.1) (D.R.rS + 1)).det =
      RealObj.Dl (Formalism.FourierDecayAlt.D.ptMatN (Bridge.lptOf σ κ D.R.rS 0 w.1) (D.R.rS + 1)) (D.R.rS + 1) :=
    (Bridge.dl_top' _).symm
  have hdet2 : (Formalism.FourierDecayAlt.D.ptMatN (Bridge.lptOf σ κ D.R.rS 0 w.1) D.R.rS).det =
      RealObj.Dl (Formalism.FourierDecayAlt.D.ptMatN (Bridge.lptOf σ κ D.R.rS 0 w.1) (D.R.rS + 1)) D.R.rS := by
    unfold RealObj.Dl; rw [dif_pos (Nat.le_succ _)]; rfl
  have hGd := Bridge.G_diag D.R.rS Y (fun a : Fin (D.R.rS + 1) => Bridge.Af κ D.R.rS a * 1)
    (fun b : Fin (D.R.rS + 1) => Formalism.L2.SG.Pf.CarrierTop.sgnV D.R.rS b * Bridge.Bf κ D.R.rS b) TT
    (by simp [Bridge.Af, Bridge.Bf, Formalism.L2.SG.Pf.CarrierTop.sgnV])
  refine ⟨(‖∏ i : Fin D.R.rS, Bridge.Af κ D.R.rS (Fin.castLE (Nat.le_succ D.R.rS) i) * 1‖ *
    ‖∏ i : Fin D.R.rS, Formalism.L2.SG.Pf.CarrierTop.sgnV D.R.rS (Fin.castLE (Nat.le_succ D.R.rS) i) *
      Bridge.Bf κ D.R.rS (Fin.castLE (Nat.le_succ D.R.rS) i)‖) ^ 2, sq_nonneg _, ?_⟩
  unfold Formalism.FourierDecayAlt.D.ptG
  rw [hdet1, hdet2, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, hM, hGd]

variable {θ : ℝ} (C : Choice X θ)

theorem rZero_carrierInT (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ)
    (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
    (fc : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j)))
    (c : Formalism.FourierDecayAlt.LE.Cut) (ν' : Fin (nfE D) → Fin (2 * D.R.rS + D.R.k + 1) → ℂ)
    (m₀ : Fin (nfE D) → Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS)
    (Θ : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TopLift D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
    (TP : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TypeProj (parE e u u' de de' j) (towersOf X C u u' e j).base.π
      (towersOf X C u u' e j).base.z (m₀ j *ᵥ ν' j)) (A₀ : ℝ)
    (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (hPRE : PtRepExists X u u' sc i0 i0') :
    RZero X (sOf (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀)) u u'
      (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀).T
      (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀).fc ν' m₀ := by
  intro p w hp hng

  obtain ⟨v, hv0⟩ : ∃ v, ‖RealObj.Dl (RealObj.ZhatO (ptC X v w)) (D.R.rS + 1)‖ ^ 2 -
      Tw (D := D) u * Tw (D := D) u' * ‖RealObj.Dl (RealObj.ZhatO (ptC X v w)) D.R.rS‖ ^ 2 ≤ 0 := by
    by_cases hrep : ∃ γ, IsPtRep X u u' w γ
    · have h1 : ¬ ∀ v, 0 < GX X u u' D.host.rdE (gamW X u u' w) v := fun h => hng ⟨hrep, h⟩
      push_neg at h1
      obtain ⟨v, hv1⟩ := h1
      refine ⟨v, ?_⟩
      have hrepw : IsPtRep X u u' w (gamW X u u' w) := by
        unfold gamW; rw [dif_pos hrep]; exact hrep.choose_spec
      have hZ1 : ZX X u u' 1 (gamW X u u' w) v = RealObj.ZhatO (ptC X v w) := by
        rw [← hrepw v, Formalism.L2.SG.Pf.CarrierTop.zhatO_invol]
      change Gv (Tw (D := D) u) (Tw (D := D) u') (ZX X u u' D.host.rdE (gamW X u u' w) v) ≤ 0 at hv1
      unfold Gv at hv1
      have hcl : Formalism.L2.SG.Pf.CarrierTop.cS D.R.rS D.host.rdE (Fin.last D.R.rS) = 1 := by
        simp [Formalism.L2.SG.Pf.CarrierTop.cS]
      have hGd := Bridge.G_diag D.R.rS (ZX X u u' 1 (gamW X u u' w) v)
        (Formalism.L2.SG.Pf.CarrierTop.cS D.R.rS D.host.rdE) (Formalism.L2.SG.Pf.CarrierTop.cS D.R.rS D.host.rdE)
        (Tw (D := D) u * Tw (D := D) u') (by rw [hcl]; simp)
      rw [Formalism.L2.SG.Pf.CarrierTop.zx_sc, hGd, hZ1] at hv1
      by_contra hpos
      push_neg at hpos
      have hrd := Formalism.MainNotions.LocalModelPeriodLattices.rdE_pos D
      have hne : (∏ i : Fin D.R.rS, Formalism.L2.SG.Pf.CarrierTop.cS D.R.rS D.host.rdE (Fin.castLE (Nat.le_succ D.R.rS) i)) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun i _ => by
          simp [Formalism.L2.SG.Pf.CarrierTop.cS, hrd.ne']
      have hc : 0 < (‖∏ i : Fin D.R.rS, Formalism.L2.SG.Pf.CarrierTop.cS D.R.rS D.host.rdE (Fin.castLE (Nat.le_succ D.R.rS) i)‖ *
          ‖∏ i : Fin D.R.rS, Formalism.L2.SG.Pf.CarrierTop.cS D.R.rS D.host.rdE (Fin.castLE (Nat.le_succ D.R.rS) i)‖) ^ 2 :=
        pow_pos (mul_pos (norm_pos_iff.mpr hne) (norm_pos_iff.mpr hne)) 2
      have := mul_pos hc hpos
      linarith
    · by_contra hall
      push_neg at hall
      obtain ⟨γ, hγ, -⟩ := hPRE w (fun v => by have := hall v; unfold Gv; exact this)
      exact hrep ⟨γ, hγ⟩
  refine ⟨(tauE X e).symm v, Or.inr ?_⟩
  set j := (tauE X e).symm v with hj
  set σ : D.host.E →+* ℂ := (X.B.I.φ v).comp X.ιE.symm.toRingHom with hσ
  set gg : ℕ := D.host.g 0 * D.host.g 1 with hggdef
  set κ : ℂ := -Complex.I * (((gg : ℝ) / (2 * Real.pi) : ℝ) : ℂ) with hκ
  have hκstar : star κ = -κ := by
    rw [hκ, star_mul', star_neg, Complex.star_def, Complex.conj_I, Complex.conj_ofReal]; ring

  have hpt := hp
  unfold ptOfL Formalism.L2.SG.DataInst.ptOfList at hpt
  split_ifs at hpt with hPtL
  have hw1 : w.1 = (Formalism.L2.SG.DataInst.signPt D.R.rS p).map Prod.swap := by
    rw [← Option.some_inj.mp hpt]; rfl
  have hfst : (Formalism.L2.SG.DataInst.signPt D.R.rS p).map Prod.fst = p.map Prod.fst :=
    Formalism.L2.SG.DataInst.sign_list_fst D.R.rS 1 p
  have hblk : ∀ b ∈ p, 1 ≤ b.1 := by
    intro b hb
    have : b.1 ∈ (Formalism.L2.SG.DataInst.signPt D.R.rS p).map Prod.fst := by
      rw [hfst]; exact List.mem_map_of_mem hb
    obtain ⟨b', hb', hbb⟩ := List.mem_map.mp this
    rw [← hbb]; exact (hPtL.2 b' hb').1
  have hsum : 0 + (p.map Prod.fst).sum ≤ D.R.rS + 1 := by rw [← hfst, hPtL.1]; omega
  have hlt := Bridge.lptOf_toStd σ D.R.rS (gg : ℝ) p 0 hblk hsum
  have hemb : (sOf (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀)).σ j = σ := by
    show embE X e j = σ
    unfold embE
    rw [hj, Equiv.apply_symm_apply]
  have hstd : Formalism.FourierDecayAlt.D.toStd D.R.rS (gg : ℝ) 1
      (Formalism.FourierDecayAlt.C.loc ((sOf (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀)).σ j) p) =
      Bridge.lptOf σ κ D.R.rS 0 w.1 := by
    rw [hemb, hw1]; exact hlt.symm
  obtain ⟨cc, hcc, hG⟩ := exists_nonneg_ptG_lptOf_eq_mul X v κ hκstar (((D.mem u).A.T : ℝ) * ((D.mem u').A.T : ℝ)) w
  unfold Formalism.FourierDecayAlt.JC.vecPlace Formalism.FourierDecayAlt.D.vecV
  rw [dif_neg]
  · simp [Formalism.FourierDecayAlt.B.hsVec]
    exact Or.inr rfl
  · rintro ⟨-, hpos⟩
    have hT := (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀).hT j
    have hT1 : Formalism.QuantumDeterminants.Tz (sOf (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀)).G.k
        (sOf (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀)).G.r
        ((carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀).T j).base.z = ((D.mem u).A.T : ℝ) :=
      hT.1
    have hT2 : Formalism.QuantumDeterminants.Tz (sOf (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀)).G.k
        (sOf (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀)).G.r
        ((carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀).T j).base.z' = ((D.mem u').A.T : ℝ) :=
      hT.2
    have hpos' : 0 < Formalism.FourierDecayAlt.D.ptG (((D.mem u).A.T : ℝ) * ((D.mem u').A.T : ℝ)) D.R.rS
        (Bridge.lptOf σ κ D.R.rS 0 w.1) := by
      convert hpos using 2
      all_goals first | rfl | exact (congrArg₂ (· * ·) hT1 hT2).symm | exact hstd.symm
    rw [hG] at hpos'
    have hpos := hpos'
    unfold Tw at hv0
    have := mul_nonpos_of_nonneg_of_nonpos hcc hv0
    linarith

end Formalism.L2.SG.Pf.Carrier.CarPinVt
