import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianInvariantCellAction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpMTop

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Filter Topology
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.GrpMA

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def LvlA : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (k r : ℕ) (hr : 1 ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp))
    (π' : Q.Mx k r → (Wq →L[ℂ] Wq)) (D' : Set (Q.Mx k r)) (Y : ℂ),
    inWb k r z → inWb k r z' → Q.IsDom k r z z' (TemperedBoundGL3.lr hr).castSucc D' →
    ∀ J₀ ∈ Q.FFl k r z z' π π' (TemperedBoundGL3.lr hr).castSucc D', ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r),
      g ∈ Qx6.Dc1 (TemperedBoundGL3.lr hr) D' c →
      NLv k r z z' (TemperedBoundGL3.lr hr).castSucc (Q.uC k r (Fin.last r) Y - 1) J₀
          (Q.w1 k r (TemperedBoundGL3.lr hr) (c (TemperedBoundGL3.lr hr)) * g) =
        -((Q.uC k r (Fin.last r) Y - 1 - ((Q.mdim k r (Fin.last r) - 1 : ℕ) : ℂ)) •
              Q.tL k r z z' (Fin.last r) Y 0 1 (fun x => J₀ (Q.w1 k r (TemperedBoundGL3.lr hr) (c (TemperedBoundGL3.lr hr)) * x)) g -
            pbOp (TemperedBoundGL3.lr hr) (fun c' => Q.tL k r z z' (Fin.last r) Y 0 1
              (fun x => J₀ (Q.w1 k r (TemperedBoundGL3.lr hr) (c' (TemperedBoundGL3.lr hr)) * x)) g) c) -
          (star (c (TemperedBoundGL3.lr hr)))⁻¹ •
            Q.tL k r z z' (Fin.last r) Y 1 1 (fun x => J₀ (Q.w1 k r (TemperedBoundGL3.lr hr) (c (TemperedBoundGL3.lr hr)) * x)) g

section ops

variable {k r : ℕ} {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem nlv_smulC (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 1)) (u : ℂ) :
    Formalism.FourierDecayAlt.P5.SmulC (E := X) (NLv k r z z' l u) := by
  intro α f
  funext x
  simp only [NLv, Pi.smul_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
  rw [Formalism.FourierDecayAlt.P5.qminorOp_smulC (fun a b => Formalism.FourierDecayAlt.P5.eabH_smulC _ a b) _ _ u α f, Pi.smul_apply, smul_comm]

theorem nlv_left {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 1))
    (u : ℂ) (i : Fin (r + 1)) {c : Fin r → ℂ} (hc : c ∈ OmX r) (f : Q.Mx k r → X) :
    NLv k r z z' l u (fun x => f (Q.wCell k r i c * x)) = fun x => NLv k r z z' l u f (Q.wCell k r i c * x) := by
  funext x
  simp only [NLv]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
  rw [TemperedBoundGL3.hermitian_invariant_cell_action i hc hz x]
  congr 1
  exact congrFun (Formalism.FourierDecayAlt.P.quantum_minor_left_hermitian X _ _ (Hpk k r) f _ _ u _) x

end ops

theorem jDRvStepA_of_lvlA (h : LvlA) : JDRvStepA := by
  intro Wp Wq _ _ _ _ k r hr z z' π π' D Y hz hz' hD J hJ c hc g hg hcg
  obtain ⟨hJ₀, hD'⟩ := TemperedBoundGL3.br1 hz hz' hD hJ hc (TemperedBoundGL3.lr hr)
  have hcg' : Q.wCell k r (TemperedBoundGL3.lr hr).succ c * g ∈ D := by rw [TemperedBoundGL3.lr_succ]; exact hcg
  have hgD' := TemperedBoundGL3.cell_preimage_mem_domain (TemperedBoundGL3.lr hr) hcg'
  have hL := h Wp Wq k r hr z z' π π' _ Y hz hz' hD' _ hJ₀ c hc g hg hgD'

  set l : Fin r := TemperedBoundGL3.lr hr with hl
  set J₀ := Q.resG k r l.castSucc J c with hJ₀def
  set W : (Fin r → ℂ) → ℂ := fun c' => ((‖c' l‖ ^ (Mdim k r l - 1) : ℝ) : ℂ) with hW
  set A' : (Fin r → ℂ) → (Wq →L[ℂ] Wp) := fun c' =>
    Q.tL k r z z' (Fin.last r) Y 0 1 (fun x => J₀ (Q.w1 k r l (c' l) * x)) g with hA'
  set T22 := Q.tL k r z z' (Fin.last r) Y 1 1 (fun x => J₀ (Q.w1 k r l (c l) * x)) g with hT22

  have hb := TemperedBoundGL3.br2 l (NLv k r z z' l.castSucc (Q.uC k r (Fin.last r) Y - 1)) (nlv_smulC z z' _ _) c
    (nlv_left hz z' _ _ l.castSucc hc) J g
  rw [TemperedBoundGL3.lr_succ] at hb
  have eL : FNv k r z z' Y J ⟨r - 1, by omega⟩ c g =
      W c • NLv k r z z' l.castSucc (Q.uC k r (Fin.last r) Y - 1) J₀ (Q.w1 k r l (c l) * g) := by
    show Q.resG k r (Fin.last r) (NLv k r z z' l.castSucc (Q.uC k r (Fin.last r) Y - 1) J) c g = _
    rw [hb]

  have eR : ∀ c' ∈ OmX r, (∀ a : Fin r, a.val < l.val → c' a = c a) →
      Q.resG k r (Fin.last r) J c' = fun x => W c' • J₀ (Q.w1 k r l (c' l) * x) := by
    intro c' hc' hcc
    rw [← TemperedBoundGL3.lr_succ hr, Qx6.resG_succ]
    funext x
    show W c' • Q.resG k r l.castSucc J c' (Q.w1 k r l (c' l) * x) = _
    rw [Qx6.ind_resG l.castSucc J c' hc' c hc (fun a ha => hcc a ha)]
  have eRc := eR c hc (fun _ _ => rfl)

  have hTop := mirror_residue_top_holds Wp Wq k r z z' π π' D Y hz hz' hD J hJ
  set f₂ : (Fin r → ℂ) → (Wq →L[ℂ] Wp) := fun c' =>
    Q.tL k r z z' (Fin.last r) Y 0 1 (Q.resG k r (Fin.last r) J c') g with hf₂
  have hgerm : (fun c' => FNv k r z z' Y J (Fin.last r) c' g) =ᶠ[𝓝 c] fun c' => -f₂ c' := by
    filter_upwards [Qx6.near_pt (Qx6.open_Dcell hD.1 (Fin.last r)) hc hcg] with c' hc'
    rw [hTop c' hc'.1 g hg hc'.2]
    rfl
  have hfam := (Formalism.FourierDecayAlt.P.restriction_good_family Wp Wq k r z z' π π' D hz hz' hD J hJ (Fin.last r)).1
  have hf₂d : DifferentiableAt ℝ f₂ c :=
    Formalism.FourierDecayAlt.P.Qx3.fam_differentiableAt (Formalism.FourierDecayAlt.P.Qx3.pres_tL z z' Y 0 1 _ hfam) (x := (c, g)) ⟨hc, hcg⟩ hg
  have hrr := Formalism.FourierDecayAlt.P.Qx3.pres_tL (i := l.succ) (U₀ := Qx6.UU (Qx6.Dc1 l (Qx6.Dcell D l.castSucc c))) z z' Y 0 1 _
    (Qx6.sf_rr Formalism.FourierDecayAlt.P.weyl_level_element_properties l hJ₀.1)
  rw [TemperedBoundGL3.lr_succ] at hrr
  have hA'd : DifferentiableAt ℝ A' c :=
    Formalism.FourierDecayAlt.P.Qx3.fam_differentiableAt hrr (x := (c, g)) ⟨hc, hgD'⟩ hg
  have hWd : DifferentiableAt ℝ W c := Qx6.diff_gamma l _ hc
  have hf₃d : DifferentiableAt ℝ (fun c' => W c' • A' c') c := hWd.smul hA'd
  have hline : ∀ᶠ s in 𝓝 (c l), (fun c' => -f₂ c') (Function.update c l s) =
      (-1 : ℂ) • (fun c' => W c' • A' c') (Function.update c l s) := by
    filter_upwards [isOpen_ne.mem_nhds (hc l)] with s hs
    have hu : Function.update c l s ∈ OmX r := Qx6.update_mem_Om hc l hs
    have hcc : ∀ a : Fin r, a.val < l.val → Function.update c l s a = c a := fun a ha =>
      Function.update_of_ne (fun e => by rw [e] at ha; exact lt_irrefl _ ha) _ _
    show -(Q.tL k r z z' (Fin.last r) Y 0 1 (Q.resG k r (Fin.last r) J (Function.update c l s)) g) = _
    rw [eR _ hu hcc, show (fun x => W (Function.update c l s) • J₀ (Q.w1 k r l (Function.update c l s l) * x)) =
      W (Function.update c l s) • (fun x => J₀ (Q.w1 k r l (Function.update c l s l) * x)) from rfl,
      Formalism.FourierDecayAlt.P5.tL_smulC z z' (Fin.last r) Y 0 1 (W (Function.update c l s))
      (fun x => J₀ (Q.w1 k r l (Function.update c l s l) * x)), neg_one_smul]
    rfl
  have hp1 : pbOp l (fun c' => FNv k r z z' Y J (Fin.last r) c' g) c = pbOp l (fun c' => -f₂ c') c :=
    Qx6.opL_germ l 3 hgerm
  have hp2 : pbOp l (fun c' => -f₂ c') c = (-1 : ℂ) • pbOp l (fun c' => W c' • A' c') c :=
    Qx6.opL_dir l 3 (-1) hf₂d.neg hf₃d hline
  have hp3 : pbOp l (fun c' => W c' • A' c') c = W c • pbOp l A' c + ((((Mdim k r l - 1 : ℕ) : ℂ) / 2) * W c) • A' c := by
    rw [Qx6.pbOp_smul l hc hWd hA'd, Qx6.pbOp_gamma l hc]

  have eF : FNv k r z z' Y J (Fin.last r) c g = -(W c • A' c) := by
    rw [hTop c hc g hg hcg]
    show -(Q.tL k r z z' (Fin.last r) Y 0 1 (Q.resG k r (Fin.last r) J c) g) = _
    rw [eRc, show (fun x => W c • J₀ (Q.w1 k r l (c l) * x)) = W c • (fun x => J₀ (Q.w1 k r l (c l) * x)) from rfl,
      Formalism.FourierDecayAlt.P5.tL_smulC z z' (Fin.last r) Y 0 1 (W c) (fun x => J₀ (Q.w1 k r l (c l) * x))]
    rfl
  have e11 : Q.QL k r z z' (Fin.last r) Y 1 1 (Q.resG k r (Fin.last r) J) c g = W c • T22 := by
    show Q.tL k r z z' (Fin.last r) Y 1 1 (Q.resG k r (Fin.last r) J c) g = _
    rw [eRc, show (fun x => W c • J₀ (Q.w1 k r l (c l) * x)) = W c • (fun x => J₀ (Q.w1 k r l (c l) * x)) from rfl,
      Formalism.FourierDecayAlt.P5.tL_smulC z z' (Fin.last r) Y 1 1 (W c) (fun x => J₀ (Q.w1 k r l (c l) * x))]
    rfl

  have hmd : ((Q.mdim k r (Fin.last r) - 1 : ℕ) : ℂ) = (Q.mdim k r (Fin.last r) : ℂ) - 1 := by
    have : 1 ≤ Q.mdim k r (Fin.last r) := by simp [Q.mdim]
    push_cast [Nat.cast_sub this]
    ring
  have hMd : ((Mdim k r l - 1 : ℕ) : ℂ) = (Q.mdim k r (Fin.last r) : ℂ) + 1 := by
    rw [Qx6.stp_Mdim, TemperedBoundGL3.lr_succ]
  have hU : Q.uC k r (Fin.last r) Y - 1 - ((Q.mdim k r (Fin.last r) - 1 : ℕ) : ℂ) =
      Y - ((Mdim k r l - 1 : ℕ) : ℂ) / 2 := by
    rw [hmd, hMd]
    unfold Q.uC
    ring

  rw [eL, hL, hU]
  show _ = Y • FNv k r z z' Y J (Fin.last r) c g - pbOp l (fun c' => FNv k r z z' Y J (Fin.last r) c' g) c -
    (star (c l))⁻¹ • Q.QL k r z z' (Fin.last r) Y 1 1 (Q.resG k r (Fin.last r) J) c g
  rw [hp1, hp2, hp3, eF, e11]
  module

end

end Formalism.FourierDecayAlt.P.CutMP.GrpMA
