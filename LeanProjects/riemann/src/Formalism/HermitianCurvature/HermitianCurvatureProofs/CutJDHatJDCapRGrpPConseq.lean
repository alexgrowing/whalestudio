import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpPCont
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HasFDerivAtFsvOther
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialRaisingTopOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SumDualVectorEqZeta
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeylCellConjTransposeMulApply
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace Formalism.FourierDecayAlt.P.CutMP

noncomputable section

section fam

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
  {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Q.Mx k r → (Wp →L[ℂ] Wp)} {π' : Q.Mx k r → (Wq →L[ℂ] Wq)}
  {Dc : (Fin r → ℂ) → Set (Q.Mx k r)}

theorem cq_add {Φ Ψ : Q.Fn k r (Wq →L[ℂ] Wp)} (h : Q.FamFF k r z z' π π' (Fin.last r) Dc Φ)
    (h' : Q.FamFF k r z z' π π' (Fin.last r) Dc Ψ) : Q.FamFF k r z z' π π' (Fin.last r) Dc (Φ + Ψ) :=
  ⟨Formalism.FourierDecayAlt.P.Qx3.sf_add h.1 h'.1, fun c hc => Formalism.FourierDecayAlt.P.Qx8.FFl_add (h.2 c hc) (h'.2 c hc)⟩

theorem cq_smul {Φ : Q.Fn k r (Wq →L[ℂ] Wp)} (h : Q.FamFF k r z z' π π' (Fin.last r) Dc Φ) (s : ℂ) :
    Q.FamFF k r z z' π π' (Fin.last r) Dc (s • Φ) :=
  ⟨Formalism.FourierDecayAlt.P.Qx3.sf_csmul s h.1, fun c hc => Formalism.FourierDecayAlt.P.Qx8.FFl_smul (h.2 c hc) s⟩

theorem cq_sub {Φ Ψ : Q.Fn k r (Wq →L[ℂ] Wp)} (h : Q.FamFF k r z z' π π' (Fin.last r) Dc Φ)
    (h' : Q.FamFF k r z z' π π' (Fin.last r) Dc Ψ) : Q.FamFF k r z z' π π' (Fin.last r) Dc (Φ - Ψ) := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ Ψ]
  exact cq_add h (cq_smul h' _)

theorem cq_opL (hz : inWb k r z) (hz' : inWb k r z') (hO : IsOpen {x : (Fin r → ℂ) × Q.Mx k r | x.1 ∈ OmX r ∧ x.2 ∈ Dc x.1})
    {Φ : Q.Fn k r (Wq →L[ℂ] Wp)} (h : Q.FamFF k r z z' π π' (Fin.last r) Dc Φ) (a : Fin r) (j : Fin 6) :
    Q.FamFF k r z z' π π' (Fin.last r) Dc (Q.crd (opL a j) Φ) :=
  Formalism.FourierDecayAlt.P.family_operators Wp Wq k r z z' π π' (Fin.last r) Dc Φ hz hz' hO h a j

end fam

section dom

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {D : Set (Q.Mx k r)}

theorem cq_open (hD : Q.IsDom k r z z' 0 D) :
    IsOpen {x : (Fin r → ℂ) × Q.Mx k r | x.1 ∈ OmX r ∧ x.2 ∈ {g | Q.wCell k r (Fin.last r) x.1 * g ∈ D}} := by
  have hw : ContDiffOn ℝ ∞ (fun c : Fin r → ℂ => Q.wCell k r (Fin.last r) c) (OmX r) :=
    Formalism.FourierDecayAlt.P.Qx3.wlist_smooth _
  have hm : ContDiffOn ℝ ∞ (fun x : (Fin r → ℂ) × Q.Mx k r => Q.wCell k r (Fin.last r) x.1 * x.2)
      {x | x.1 ∈ OmX r} :=
    Formalism.FourierDecayAlt.P.Qx3.cdo_mul (hw.comp contDiff_fst.contDiffOn (fun _ h => h)) contDiff_snd.contDiffOn
  exact hm.continuousOn.isOpen_inter_preimage Formalism.FourierDecayAlt.P.Qx3.isOpen_OmXX hD.1

theorem cq_isDom (hD : Q.IsDom k r z z' 0 D) {c : Fin r → ℂ} (hc : c ∈ OmX r) :
    Q.IsDom k r z z' (Fin.last r) {g | Q.wCell k r (Fin.last r) c * g ∈ D} := by
  refine ⟨hD.1.preimage (continuous_const.matrix_mul continuous_id), ?_⟩
  rintro g ⟨hgG, hgD⟩ s ⟨h, hh, m, hm, rfl⟩ s' ⟨h', hh', m', hm', rfl⟩
  have hhm : h * m ∈ Q.Glev k r (Fin.last r) :=
    Formalism.FourierDecayAlt.P.Qx3.glev_mul (Formalism.FourierDecayAlt.P.Qx3.uw_glev _ hh) hm.2
  have hcomm : Q.wCell k r (Fin.last r) c * (h * m) = (h * m) * Q.wCell k r (Fin.last r) c :=
    Formalism.FourierDecayAlt.P.Qx3.wlist_comm (Fin.last r) c _ (fun a _ => a.isLt) hhm
  have hwg : Q.wCell k r (Fin.last r) c * g ∈ Q.Glev k r 0 :=
    Formalism.FourierDecayAlt.P.Qx3.glev_mul (Formalism.FourierDecayAlt.P.Qx3.wlist_glev hc _)
      (Formalism.FourierDecayAlt.P.Qx3.glev_mono (Fin.zero_le _) hgG)
  have e : Q.wCell k r (Fin.last r) c * (h * m * g * (h' * m')) =
      h * m * (Q.wCell k r (Fin.last r) c * g) * (h' * m') := by
    rw [← Matrix.mul_assoc (Q.wCell k r (Fin.last r) c), ← Matrix.mul_assoc (Q.wCell k r (Fin.last r) c),
      hcomm, Matrix.mul_assoc (h * m)]
  show Q.wCell k r (Fin.last r) c * (h * m * g * (h' * m')) ∈ D
  rw [e]
  exact hD.2 _ ⟨hwg, hgD⟩ _ ⟨h, hh, m, ⟨hm.1, Formalism.FourierDecayAlt.P.Qx3.glev_mono (Fin.zero_le _) hm.2⟩, rfl⟩ _
    ⟨h', hh', m', ⟨hm'.1, Formalism.FourierDecayAlt.P.Qx3.glev_mono (Fin.zero_le _) hm'.2⟩, rfl⟩

end dom

section pop

variable {r : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem cq_pOp_loc (l : Fin r) {f₁ f₂ : (Fin r → ℂ) → X} {c : Fin r → ℂ} (hev : f₁ =ᶠ[nhds c] f₂) :
    pOp l f₁ c = pOp l f₂ c := by
  simp only [pOp, wirt, hev.fderiv_eq]

theorem cq_pOp_neg_add (l : Fin r) {f₁ f₂ : (Fin r → ℂ) → X} {c : Fin r → ℂ} (h₁ : DifferentiableAt ℝ f₁ c)
    (h₂ : DifferentiableAt ℝ f₂ c) :
    pOp l (fun c' => -(f₁ c' + f₂ c')) c = -(pOp l f₁ c + pOp l f₂ c) := by
  have e : (fun c' => -(f₁ c' + f₂ c')) = -(f₁ + f₂) := rfl
  simp only [pOp, wirt]
  split_ifs
  · rw [e, fderiv_neg, fderiv_add h₁ h₂]
    simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.add_apply]
    module
  · simp

end pop

section smooth

variable {k r : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem cq_contDiffAt {U₀ : Set ((Fin r → ℂ) × Q.Mx k r)} {Φ : Q.Fn k r X}
    (h : Q.SmoothFam k r (Fin.last r) U₀ Φ) {c : Fin r → ℂ} {g : Q.Mx k r} (hx : (c, g) ∈ U₀)
    (hg : g ∈ Q.Glev k r (Fin.last r)) : ContDiffAt ℝ ∞ (fun c' => Φ c' g) c := by
  obtain ⟨U, F, hU, hxU, hF, hEq⟩ := h (c, g) hx hg
  have hcont : Continuous (fun c' : Fin r → ℂ => (c', g)) := continuous_id.prodMk continuous_const
  have hev : (fun c' => Φ c' g) =ᶠ[nhds c] (fun c' => F (c', g)) := by
    filter_upwards [hcont.continuousAt.preimage_mem_nhds (hU.mem_nhds hxU)] with c' hc'
    exact hEq (c', g) hc' hg
  refine ContDiffAt.congr_of_eventuallyEq ?_ hev
  exact (hF.contDiffAt (hU.mem_nhds hxU)).comp c (contDiff_id.prodMk contDiff_const).contDiffAt

end smooth

section main

theorem cq_pOp_neg {r : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] (l : Fin r)
    {f : (Fin r → ℂ) → X} {c : Fin r → ℂ} : pOp l (fun c' => -f c') c = -pOp l f c := by
  have e : (fun c' => -f c') = -f := rfl
  simp only [pOp, wirt]
  split_ifs
  · rw [e, fderiv_neg]
    simp only [neg_apply]
    module
  · simp

theorem jDRConseq_of (hP : JDRPComm) (hC : JDRCont) : JDRConseq := by
  intro hT hA hS Wp Wq _ _ _ _ k r z z' π π' D Y hz hz' hD J hJ
  set Dc : (Fin r → ℂ) → Set (Q.Mx k r) := fun c => {g | Q.wCell k r (Fin.last r) c * g ∈ D} with hDc
  set Φ := Q.resG k r (Fin.last r) J with hΦdef
  have hO : IsOpen {x : (Fin r → ℂ) × Q.Mx k r | x.1 ∈ OmX r ∧ x.2 ∈ Dc x.1} := cq_open hD
  have hFam : Q.FamFF k r z z' π π' (Fin.last r) Dc Φ :=
    Formalism.FourierDecayAlt.P.restriction_good_family Wp Wq k r z z' π π' D hz hz' hD J hJ (Fin.last r)

  set Ψ : ℕ → Fin 2 → Q.Fn k r (Wq →L[ℂ] Wp) := fun m b => Q.crd (tdU r Y m b) Φ with hΨdef
  have eΨ00 : Ψ 0 0 = Φ := by funext c g; simp [hΨdef, tdU, Q.crd]
  have eΨ01 : Ψ 0 1 = (0 : ℂ) • Φ := by funext c g; simp [hΨdef, tdU, Q.crd]
  have eΨ10 : ∀ h : 1 ≤ r, Ψ 1 0 = Y • Φ + Q.crd (pOp ⟨r - 1, by omega⟩) Φ := by
    intro h; funext c g; simp [hΨdef, tdU, Q.crd, h]
  have eΨ11 : ∀ h : 1 ≤ r, Ψ 1 1 = Q.crd (ciOp ⟨r - 1, by omega⟩) Φ := by
    intro h; funext c g; simp [hΨdef, tdU, Q.crd, h]
  have eΨ2 : ∀ (m : ℕ) (h : m + 2 ≤ r) (b : Fin 2), Ψ (m + 2) b =
      Y • Ψ (m + 1) b + Q.crd (pOp ⟨r - (m + 2), by omega⟩) (Ψ (m + 1) b) -
        Q.crd (cOp ⟨r - (m + 1), by omega⟩) (Q.crd (ciOp ⟨r - (m + 2), by omega⟩) (Ψ m b)) := by
    intro m h b; funext c g; simp only [hΨdef, tdU, dif_pos h, Q.crd, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  have famΨ : ∀ m, m ≤ r → ∀ b, Q.FamFF k r z z' π π' (Fin.last r) Dc (Ψ m b) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
    intro hm b
    rcases m with _ | _ | m
    · fin_cases b
      · simpa [eΨ00] using hFam
      · simpa [eΨ01] using cq_smul hFam 0
    · fin_cases b
      · show Q.FamFF k r z z' π π' (Fin.last r) Dc (Ψ 1 0)
        rw [eΨ10 hm]
        exact cq_add (cq_smul hFam Y) (cq_opL hz hz' hO hFam _ 0)
      · show Q.FamFF k r z z' π π' (Fin.last r) Dc (Ψ 1 1)
        rw [eΨ11 hm]
        exact cq_opL hz hz' hO hFam _ 2
    · rw [eΨ2 m hm b]
      exact cq_sub (cq_add (cq_smul (ih (m + 1) (by omega) (by omega) b) Y)
        (cq_opL hz hz' hO (ih (m + 1) (by omega) (by omega) b) _ 0))
        (cq_opL hz hz' hO (cq_opL hz hz' hO (ih m (by omega) (by omega) b) _ 2) _ 1)

  have hQLfam : ∀ F : Q.Fn k r (Wq →L[ℂ] Wp), Q.FamFF k r z z' π π' (Fin.last r) Dc F → ∀ a b : Fin 2,
      Q.FamFF k r z z' π π' (Fin.last r) Dc (Q.QL k r z z' (Fin.last r) Y a b F) := fun F hF a b =>
    ⟨Formalism.FourierDecayAlt.P.transfer_joint_smooth (Wq →L[ℂ] Wp) k r z z' (Fin.last r) _ F Y a b hO hF.1,
      fun c hc => Formalism.FourierDecayAlt.P.operator_preserves_fusion_forms Wp Wq k r z z' π π' (Fin.last r) (Dc c) Y a b hz hz'
        (cq_isDom hD hc) _ (hF.2 c hc)⟩
  have hlin : ∀ (a b : Fin 2) (c : Fin r → ℂ), c ∈ OmX r → ∀ (f f₂ : Q.Mx k r → (Wq →L[ℂ] Wp)) (s : ℂ),
      Q.SmoothLev k r (Fin.last r) (Dc c) f → Q.SmoothLev k r (Fin.last r) (Dc c) f₂ →
      ∀ g ∈ Q.Glev k r (Fin.last r), g ∈ Dc c →
        Q.tL k r z z' (Fin.last r) Y a b (fun x => f x + s • f₂ x) g =
          Q.tL k r z z' (Fin.last r) Y a b f g + s • Q.tL k r z z' (Fin.last r) Y a b f₂ g :=
    fun a b c hc f f₂ s hf hf₂ g hg hgD =>
      (Formalism.FourierDecayAlt.P.transfer_linear_local (Wq →L[ℂ] Wp) k r z z' (Fin.last r) (Dc c) Y a b f f₂ s
        (cq_isDom hD hc).1 hf hf₂ g ⟨hg, hgD⟩).1
  have hsm : ∀ (a b : Fin 2) (f : Q.Mx k r → (Wq →L[ℂ] Wp)) (s : ℂ) (g : Q.Mx k r),
      Q.tL k r z z' (Fin.last r) Y a b (fun x => s • f x) g = s • Q.tL k r z z' (Fin.last r) Y a b f g := by
    intro a b f s g
    have := Formalism.FourierDecayAlt.P5.tL_smulC (E := Wq →L[ℂ] Wp) z z' (Fin.last r) Y a b s f
    exact congrFun this g
  have hnb : ∀ c ∈ OmX r, ∀ g : Q.Mx k r, g ∈ Dc c → {c' | c' ∈ OmX r ∧ g ∈ Dc c'} ∈ nhds c := by
    intro c hc g hgD
    have hcont : Continuous (fun c' : Fin r → ℂ => (c', g)) := continuous_id.prodMk continuous_const
    exact (hO.preimage hcont).mem_nhds ⟨hc, hgD⟩
  have hdiff : ∀ F : Q.Fn k r (Wq →L[ℂ] Wp), Q.FamFF k r z z' π π' (Fin.last r) Dc F →
      ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r), g ∈ Dc c → DifferentiableAt ℝ (fun c' => F c' g) c :=
    fun F hF c hc g hg hgD => (cq_contDiffAt hF.1 ⟨hc, hgD⟩ hg).differentiableAt (by simp)

  have key : ∀ m, m ≤ r → ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r), Q.wCell k r (Fin.last r) c * g ∈ D →
      FN k r z z' Y J ⟨r - m, by omega⟩ c g =
        -(Q.QL k r z z' (Fin.last r) Y 1 0 (Ψ m 0) c g + Q.QL k r z z' (Fin.last r) Y 1 1 (Ψ m 1) c g) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
    intro hm c hc g hg hcg
    rcases m with _ | _ | m
    · have h := hT Wp Wq k r z z' π π' D Y hz hz' hD J hJ c hc g hg hcg
      have e : (⟨r - 0, by omega⟩ : Fin (r + 1)) = Fin.last r := Fin.ext (by simp)
      rw [e, h, eΨ00, eΨ01]
      have h0 : Q.QL k r z z' (Fin.last r) Y 1 1 ((0 : ℂ) • Φ) c g = 0 := by
        show Q.tL k r z z' (Fin.last r) Y 1 1 (fun x => (0 : ℂ) • Φ c x) g = 0
        rw [hsm, zero_smul]
      rw [h0, add_zero]
    ·
      have h := hA Wp Wq k r hm z z' π π' D Y hz hz' hD J hJ c hc g hg hcg
      have e : (⟨r - (0 + 1), by omega⟩ : Fin (r + 1)) = ⟨r - 1, by omega⟩ := rfl
      rw [e, h]
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Q.crd]
      have hTop : ∀ c' ∈ OmX r, g ∈ Dc c' →
          FN k r z z' Y J (Fin.last r) c' g = -Q.QL k r z z' (Fin.last r) Y 1 0 Φ c' g :=
        fun c' hc' hgD' => hT Wp Wq k r z z' π π' D Y hz hz' hD J hJ c' hc' g hg hgD'
      have hev : (fun c' => FN k r z z' Y J (Fin.last r) c' g) =ᶠ[nhds c]
          (fun c' => -Q.QL k r z z' (Fin.last r) Y 1 0 Φ c' g) := by
        filter_upwards [hnb c hc g hcg] with c' hc'
        exact hTop c' hc'.1 hc'.2
      rw [cq_pOp_loc _ hev, cq_pOp_neg, hTop c hc hcg]
      have hpc := hP Wp Wq k r z z' π π' Dc Φ hz hz' hO hFam ⟨r - 1, by omega⟩ Y 1 0 c hc g hg hcg
      simp only [Q.crd] at hpc
      rw [hpc, eΨ10 hm, eΨ11 hm]
      have e2 : Q.QL k r z z' (Fin.last r) Y 1 0 (Y • Φ + Q.crd (pOp ⟨r - 1, by omega⟩) Φ) c g =
          Q.QL k r z z' (Fin.last r) Y 1 0 (Q.crd (pOp ⟨r - 1, by omega⟩) Φ) c g +
            Y • Q.QL k r z z' (Fin.last r) Y 1 0 Φ c g := by
        show Q.tL k r z z' (Fin.last r) Y 1 0 (fun x => Y • Φ c x + Q.crd (pOp ⟨r - 1, by omega⟩) Φ c x) g = _
        have e3 : (fun x => Y • Φ c x + Q.crd (pOp ⟨r - 1, by omega⟩) Φ c x) =
            (fun x => Q.crd (pOp ⟨r - 1, by omega⟩) Φ c x + Y • Φ c x) := by funext x; rw [add_comm]
        rw [e3, hlin 1 0 c hc (Q.crd (pOp ⟨r - 1, by omega⟩) Φ c) (Φ c) Y ((cq_opL hz hz' hO hFam _ 0).2 c hc).1
          (hFam.2 c hc).1 g hg hcg]
        rfl
      have e4 : Q.QL k r z z' (Fin.last r) Y 1 1 (Q.crd (ciOp ⟨r - 1, by omega⟩) Φ) c g =
          (c ⟨r - 1, by omega⟩)⁻¹ • Q.QL k r z z' (Fin.last r) Y 1 1 Φ c g := by
        show Q.tL k r z z' (Fin.last r) Y 1 1 (fun x => (c ⟨r - 1, by omega⟩)⁻¹ • Φ c x) g = _
        rw [hsm]
        rfl
      rw [e2, e4]
      simp only [ciOp]
      module
    ·
      have hm' : m + 2 ≤ r := hm
      have h := hS Wp Wq k r z z' π π' D Y hz hz' hD J hJ (r - (m + 2)) (by omega) c hc g hg hcg
      have e1 : (⟨r - (m + 2) + 1, by omega⟩ : Fin (r + 1)) = ⟨r - (m + 1), by omega⟩ := Fin.ext (by simp; omega)
      have e2 : (⟨r - (m + 2) + 2, by omega⟩ : Fin (r + 1)) = ⟨r - m, by omega⟩ := Fin.ext (by simp; omega)
      have e1' : (⟨r - (m + 2) + 1, by omega⟩ : Fin r) = ⟨r - (m + 1), by omega⟩ := Fin.ext (by simp; omega)
      rw [e1, e2, e1'] at h
      have e0 : (⟨r - (m + 1 + 1), by omega⟩ : Fin (r + 1)) = ⟨r - (m + 2), by omega⟩ := rfl
      rw [e0, h]
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Q.crd, cOp, ciOp]
      have ih1 := ih (m + 1) (by omega) (by omega)
      have ih0 := ih m (by omega) (by omega)
      have hF0 := famΨ (m + 1) (by omega) 0
      have hF1 := famΨ (m + 1) (by omega) 1
      have hev : (fun c' => FN k r z z' Y J ⟨r - (m + 1), by omega⟩ c' g) =ᶠ[nhds c]
          (fun c' => -(Q.QL k r z z' (Fin.last r) Y 1 0 (Ψ (m + 1) 0) c' g +
            Q.QL k r z z' (Fin.last r) Y 1 1 (Ψ (m + 1) 1) c' g)) := by
        filter_upwards [hnb c hc g hcg] with c' hc'
        exact ih1 c' hc'.1 g hg hc'.2
      rw [cq_pOp_loc _ hev, cq_pOp_neg_add _ (hdiff _ (hQLfam _ hF0 1 0) c hc g hg hcg)
        (hdiff _ (hQLfam _ hF1 1 1) c hc g hg hcg)]
      have hp0 := hP Wp Wq k r z z' π π' Dc (Ψ (m + 1) 0) hz hz' hO hF0 ⟨r - (m + 2), by omega⟩ Y 1 0 c hc g hg hcg
      have hp1 := hP Wp Wq k r z z' π π' Dc (Ψ (m + 1) 1) hz hz' hO hF1 ⟨r - (m + 2), by omega⟩ Y 1 1 c hc g hg hcg
      simp only [Q.crd] at hp0 hp1
      rw [hp0, hp1, ih1 c hc g hg hcg, ih0 c hc g hg hcg]
      have hR : ∀ b : Fin 2, Q.QL k r z z' (Fin.last r) Y 1 b (Ψ (m + 2) b) c g =
          (Q.QL k r z z' (Fin.last r) Y 1 b (Q.crd (pOp ⟨r - (m + 2), by omega⟩) (Ψ (m + 1) b)) c g +
            Y • Q.QL k r z z' (Fin.last r) Y 1 b (Ψ (m + 1) b) c g) +
          (-(c ⟨r - (m + 1), by omega⟩ * (c ⟨r - (m + 2), by omega⟩)⁻¹)) •
            Q.QL k r z z' (Fin.last r) Y 1 b (Ψ m b) c g := by
        intro b
        have hA' := famΨ (m + 1) (by omega) b
        have hB' := famΨ m (by omega) b
        have hPA := cq_opL hz hz' hO hA' ⟨r - (m + 2), by omega⟩ 0
        show Q.tL k r z z' (Fin.last r) Y 1 b (Ψ (m + 2) b c) g = _
        have e5 : Ψ (m + 2) b c = fun x => (Q.crd (pOp ⟨r - (m + 2), by omega⟩) (Ψ (m + 1) b) c x +
            Y • Ψ (m + 1) b c x) + (-(c ⟨r - (m + 1), by omega⟩ * (c ⟨r - (m + 2), by omega⟩)⁻¹)) • Ψ m b c x := by
          rw [eΨ2 m hm' b]
          funext x
          simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Q.crd, cOp, ciOp]
          module
        rw [e5, hlin 1 b c hc (fun x => Q.crd (pOp ⟨r - (m + 2), by omega⟩) (Ψ (m + 1) b) c x + Y • Ψ (m + 1) b c x)
          (Ψ m b c) _ ((cq_add hPA (cq_smul hA' Y)).2 c hc).1 (hB'.2 c hc).1 g hg hcg,
          hlin 1 b c hc (Q.crd (pOp ⟨r - (m + 2), by omega⟩) (Ψ (m + 1) b) c) (Ψ (m + 1) b c) Y (hPA.2 c hc).1
            (hA'.2 c hc).1 g hg hcg]
        rfl
      rw [hR 0, hR 1]
      module

  have famV : ∀ i, i ≤ r → Q.FamFF k r z z' π π' (Fin.last r) Dc (Q.crd (Q.vAB r Y i).1 Φ) ∧
      Q.FamFF k r z z' π π' (Fin.last r) Dc (Q.crd (Q.vAB r Y i).2 Φ) := by
    intro i
    induction i with
    | zero =>
      intro _
      refine ⟨?_, ?_⟩
      · have e : Q.crd (Q.vAB r Y 0).1 Φ = Φ := by funext c g; rfl
        rw [e]; exact hFam
      · have e : Q.crd (Q.vAB r Y 0).2 Φ = (0 : ℂ) • Φ := by funext c g; simp [Q.vAB, Q.crd]
        rw [e]; exact cq_smul hFam 0
    | succ i ih =>
      intro hi
      obtain ⟨hA', hB'⟩ := ih (by omega)
      have hlt : i < r := by omega
      refine ⟨?_, ?_⟩
      · have e : Q.crd (Q.vAB r Y (i + 1)).1 Φ = Y • Q.crd (Q.vAB r Y i).1 Φ +
            Q.crd (pOp ⟨i, hlt⟩) (Q.crd (Q.vAB r Y i).1 Φ) - Q.crd (cOp ⟨i, hlt⟩) (Q.crd (Q.vAB r Y i).2 Φ) := by
          funext c g; simp only [Q.vAB, dif_pos hlt, Q.crd, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
        rw [e]
        exact cq_sub (cq_add (cq_smul hA' Y) (cq_opL hz hz' hO hA' _ 0)) (cq_opL hz hz' hO hB' _ 1)
      · have e : Q.crd (Q.vAB r Y (i + 1)).2 Φ = Q.crd (ciOp ⟨i, hlt⟩) (Q.crd (Q.vAB r Y i).1 Φ) := by
          funext c g; simp only [Q.vAB, dif_pos hlt, Q.crd]
        rw [e]
        exact cq_opL hz hz' hO hA' _ 2
  have famVb : ∀ b : Fin 2, Q.FamFF k r z z' π π' (Fin.last r) Dc (Q.crd (Q.cmp (Q.vAB r Y r) b) Φ) := by
    intro b
    fin_cases b
    · exact (famV r le_rfl).1
    · exact (famV r le_rfl).2
  intro c hc g hg hcg
  have hk := key r le_rfl c hc g hg hcg
  have e : (⟨r - r, by omega⟩ : Fin (r + 1)) = 0 := Fin.ext (by simp)
  rw [e] at hk
  rw [hk]
  have hsw : ∀ b : Fin 2, Q.QL k r z z' (Fin.last r) Y 1 b (Ψ r b) c g =
      Q.QL k r z z' (Fin.last r) Y 1 b (Q.crd (Q.cmp (Q.vAB r Y r) b) Φ) c g := by
    intro b
    refine (Formalism.FourierDecayAlt.P.transfer_linear_local (Wq →L[ℂ] Wp) k r z z' (Fin.last r) (Dc c) Y 1 b (Ψ r b c)
      (Q.crd (Q.cmp (Q.vAB r Y r) b) Φ c) 0 (cq_isDom hD hc).1 ((famΨ r le_rfl b).2 c hc).1
      ((famVb b).2 c hc).1 g ⟨hg, hcg⟩).2 ?_
    intro x hx
    have hOx : IsOpen {c' : Fin r → ℂ | c' ∈ OmX r ∧ x ∈ Dc c'} :=
      hO.preimage (continuous_id.prodMk continuous_const)
    have hsmooth : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun c' => Φ c' x) {c' | c' ∈ OmX r ∧ x ∈ Dc c'} :=
      fun c' hc' => (cq_contDiffAt hFam.1 hc' hx.1).contDiffWithinAt
    exact hC (Wq →L[ℂ] Wp) r Y _ hOx (fun c' hc' => hc'.1) (fun c' => Φ c' x) hsmooth c ⟨hc, hx.2⟩ b
  simp only [Pi.neg_apply, Pi.add_apply]
  rw [hsw 0, hsw 1]

end main

end

end Formalism.FourierDecayAlt.P.CutMP
