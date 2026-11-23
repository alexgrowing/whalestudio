import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadAATopOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellValues

open MeasureTheory Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBN

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section loc

variable {r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem pOp_locO (l : Fin r) {f₁ f₂ : (Fin r → ℂ) → E} (h : ∀ c ∈ OmX r, f₁ c = f₂ c) {c : Fin r → ℂ}
    (hc : c ∈ OmX r) : pOp l f₁ c = pOp l f₂ c := by
  have hev : f₁ =ᶠ[nhds c] f₂ := by
    filter_upwards [(Formalism.FourierDecayAlt.P.Qx3.isOpen_OmX r).mem_nhds hc] with c' hc' using h c' hc'
  simp only [pOp, wirt, if_pos hc, hev.fderiv_eq]

theorem vAB_loc (Y : ℂ) : ∀ (i : ℕ) (f₁ f₂ : (Fin r → ℂ) → E), (∀ c ∈ OmX r, f₁ c = f₂ c) →
    ∀ c ∈ OmX r, (Q.vAB r Y i).1 f₁ c = (Q.vAB r Y i).1 f₂ c ∧ (Q.vAB r Y i).2 f₁ c = (Q.vAB r Y i).2 f₂ c
  | 0, f₁, f₂, h, c, hc => ⟨h c hc, rfl⟩
  | i + 1, f₁, f₂, h, c, hc => by
    have ih := vAB_loc Y i f₁ f₂ h
    by_cases hi : i < r
    · simp only [Q.vAB, dif_pos hi]
      refine ⟨?_, ?_⟩
      · simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, cOp]
        rw [(ih c hc).1, (ih c hc).2, pOp_locO _ (fun c' hc' => (ih c' hc').1) hc]
      · simp only [ciOp]
        rw [(ih c hc).1]
    · simp only [Q.vAB, dif_neg hi]
      exact ih c hc

end loc

section jd

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem jf_dinv (Bs : B.RealPlaceData k r Wp Wq) (H : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r) :
    B.JF Bs (fun x => (Dmin k r Bs.z Bs.z' x (Fin.last _))⁻¹ • H x) g =
      (Dmin k r Bs.z Bs.z' g (Fin.last _))⁻¹ • B.JF Bs H g := by
  show ∫ p, JF.xiP Bs p • B.rho Bs p (fun x => (Dmin k r Bs.z Bs.z' x (Fin.last _))⁻¹ • H x) g ∂Bs.μSS =
    (Dmin k r Bs.z Bs.z' g (Fin.last _))⁻¹ • ∫ p, JF.xiP Bs p • B.rho Bs p H g ∂Bs.μSS
  rw [← integral_smul]
  refine integral_congr_ae ?_
  filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS Bs] with p hp
  simp only [B.rho]
  rw [Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs Bs hp, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_comm]

end jd

end Formalism.FourierDecayAlt.P.PBN

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.PBN

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem radial_raising_top_of_parts : PBN.RadAATopOfParts := by
  intro hJ hC hM hR hCp Wp Wq _ _ _ _ _ _ P Bs X μ L st l0 y hD F hF
  refine ⟨hCp P.k P.r Wp Wq Bs F y hF, fun Φ hΦ x hx => ?_⟩
  have hL : Q.IsActualLevel X L := hD.2.2.1
  have hc0 : (∏ a, x.1 a) ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => hx.1 a
  have hcell := Formalism.FourierDecayAlt.P.big_cell_values P.k P.r Wp Wq Bs x hx
  have hγ := Formalism.FourierDecayAlt.P.TLB.wCell_om Bs hx

  have e1 : (TL.aP L (y : ℂ)).1 Φ = (L.ζi).1 ((L.Ar (y : ℂ)).1 Φ) := rfl
  rw [e1, hL.2.2.2.2.2.2.2.1]
  show ((X.fn 1 ((L.Ar (y : ℂ)).1 Φ) : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :
    Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 = _
  rw [X.fn_apply 1 _ x hx, hR P.k P.r Bs.z Bs.z' Wp Wq Bs.π Bs.π' X L (y : ℂ) hL Φ x hx]
  have eΦ : Q.crd (Q.vAB P.r (y : ℂ) P.r).1 (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 =
      Q.crd (Q.vAB P.r (y : ℂ) P.r).1 (Q.resG P.k P.r (Fin.last P.r) (B.JF Bs F)) x.1 x.2 :=
    (vAB_loc (y : ℂ) P.r _ _ (fun c' hc' => hΦ (c', x.2) ⟨hc', hx.2⟩) x.1 hx.1).1
  rw [eΦ, ← hM P.k P.r Wp Wq Bs F (y : ℂ) hF x hx]

  simp only [Q.resG]
  have eJ : B.JF Bs (aaTop Bs y F) (Q.wCell P.k P.r (Fin.last P.r) x.1 * x.2) =
      (Q.zetaL P.k P.r Bs.z Bs.z' (Fin.last P.r) x.2)⁻¹ •
        qminorOp (EabH (Hpk P.k P.r)) (C3.xR P.k P.r P.r le_rfl) (C3.xR P.k P.r P.r le_rfl)
          ((y : ℂ) + ((2 * P.r + P.k : ℕ) : ℂ) / 2) (B.JF Bs F) (Q.wCell P.k P.r (Fin.last P.r) x.1 * x.2) := by
    unfold aaTop
    rw [jf_dinv, hJ P.k P.r Wp Wq Bs F _ hF _ hγ, hC P.k P.r _ _ _ _ _ hx.2.1, hcell.2.2.1, smul_smul]
    congr 1
    rw [mul_inv, mul_comm, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
  rw [eJ, smul_comm]
  rfl

end Formalism.FourierDecayAlt.P
