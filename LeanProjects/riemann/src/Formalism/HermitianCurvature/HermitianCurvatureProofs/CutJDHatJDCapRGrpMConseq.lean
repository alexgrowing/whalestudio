import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpMCont
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpPConseq
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpPPCommPf

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace Formalism.FourierDecayAlt.P.CutMP

noncomputable section

section pbop

variable {r : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem vcq_pbOp_loc (l : Fin r) {f₁ f₂ : (Fin r → ℂ) → X} {c : Fin r → ℂ} (hev : f₁ =ᶠ[nhds c] f₂) :
    pbOp l f₁ c = pbOp l f₂ c := by
  simp only [pbOp, wirtBar, hev.fderiv_eq]

theorem vcq_pbOp_neg (l : Fin r) {f : (Fin r → ℂ) → X} {c : Fin r → ℂ} : pbOp l (fun c' => -f c') c = -pbOp l f c := by
  have e : (fun c' => -f c') = -f := rfl
  simp only [pbOp, wirtBar]
  split_ifs
  · rw [e, fderiv_neg]
    simp only [neg_apply]
    module
  · simp

theorem vcq_pbOp_neg_add (l : Fin r) {f₁ f₂ : (Fin r → ℂ) → X} {c : Fin r → ℂ} (h₁ : DifferentiableAt ℝ f₁ c)
    (h₂ : DifferentiableAt ℝ f₂ c) :
    pbOp l (fun c' => -(f₁ c' + f₂ c')) c = -(pbOp l f₁ c + pbOp l f₂ c) := by
  have e : (fun c' => -(f₁ c' + f₂ c')) = -(f₁ + f₂) := rfl
  simp only [pbOp, wirtBar]
  split_ifs
  · rw [e, fderiv_neg, fderiv_add h₁ h₂]
    simp only [neg_apply, ContinuousLinearMap.add_apply]
    module
  · simp

end pbop

theorem jDRvConseq_of (hC : JDRvCont) : JDRvConseq := by
  intro hT hA hS Wp Wq _ _ _ _ k r z z' π π' D Y hz hz' hD J hJ
  have hP := crd_pbOp_QL_last_comm
  set Dc : (Fin r → ℂ) → Set (Q.Mx k r) := fun c => {g | Q.wCell k r (Fin.last r) c * g ∈ D} with hDc
  set Φ := Q.resG k r (Fin.last r) J with hΦdef
  have hO : IsOpen {x : (Fin r → ℂ) × Q.Mx k r | x.1 ∈ OmX r ∧ x.2 ∈ Dc x.1} := cq_open hD
  have hFam : Q.FamFF k r z z' π π' (Fin.last r) Dc Φ :=
    Formalism.FourierDecayAlt.P.restriction_good_family Wp Wq k r z z' π π' D hz hz' hD J hJ (Fin.last r)
  set Ψ : ℕ → Fin 2 → Q.Fn k r (Wq →L[ℂ] Wp) := fun m b => Q.crd (tdUv r Y m b) Φ with hΨdef
  have eΨ00 : Ψ 0 0 = Φ := by funext c g; simp [hΨdef, tdUv, Q.crd]
  have eΨ01 : Ψ 0 1 = (0 : ℂ) • Φ := by funext c g; simp [hΨdef, tdUv, Q.crd]
  have eΨ10 : ∀ h : 1 ≤ r, Ψ 1 0 = Y • Φ - Q.crd (pbOp ⟨r - 1, by omega⟩) Φ := by
    intro h; funext c g; simp [hΨdef, tdUv, Q.crd, h]
  have eΨ11 : ∀ h : 1 ≤ r, Ψ 1 1 = Q.crd (cbiOp ⟨r - 1, by omega⟩) Φ := by
    intro h; funext c g; simp [hΨdef, tdUv, Q.crd, h]
  have eΨ2 : ∀ (m : ℕ) (h : m + 2 ≤ r) (b : Fin 2), Ψ (m + 2) b =
      Y • Ψ (m + 1) b - Q.crd (pbOp ⟨r - (m + 2), by omega⟩) (Ψ (m + 1) b) -
        Q.crd (cbOp ⟨r - (m + 1), by omega⟩) (Q.crd (cbiOp ⟨r - (m + 2), by omega⟩) (Ψ m b)) := by
    intro m h b; funext c g; simp only [hΨdef, tdUv, dif_pos h, Q.crd, Pi.sub_apply, Pi.smul_apply]
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
        exact cq_sub (cq_smul hFam Y) (cq_opL hz hz' hO hFam _ 3)
      · show Q.FamFF k r z z' π π' (Fin.last r) Dc (Ψ 1 1)
        rw [eΨ11 hm]
        exact cq_opL hz hz' hO hFam _ 5
    · rw [eΨ2 m hm b]
      exact cq_sub (cq_sub (cq_smul (ih (m + 1) (by omega) (by omega) b) Y)
        (cq_opL hz hz' hO (ih (m + 1) (by omega) (by omega) b) _ 3))
        (cq_opL hz hz' hO (cq_opL hz hz' hO (ih m (by omega) (by omega) b) _ 5) _ 4)
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
      FNv k r z z' Y J ⟨r - m, by omega⟩ c g =
        -(Q.QL k r z z' (Fin.last r) Y 0 1 (Ψ m 0) c g + Q.QL k r z z' (Fin.last r) Y 1 1 (Ψ m 1) c g) := by
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
    · have h := hA Wp Wq k r hm z z' π π' D Y hz hz' hD J hJ c hc g hg hcg
      have e : (⟨r - (0 + 1), by omega⟩ : Fin (r + 1)) = ⟨r - 1, by omega⟩ := rfl
      rw [e, h]
      simp only [Pi.sub_apply, Pi.smul_apply, Q.crd]
      have hTop : ∀ c' ∈ OmX r, g ∈ Dc c' →
          FNv k r z z' Y J (Fin.last r) c' g = -Q.QL k r z z' (Fin.last r) Y 0 1 Φ c' g :=
        fun c' hc' hgD' => hT Wp Wq k r z z' π π' D Y hz hz' hD J hJ c' hc' g hg hgD'
      have hev : (fun c' => FNv k r z z' Y J (Fin.last r) c' g) =ᶠ[nhds c]
          (fun c' => -Q.QL k r z z' (Fin.last r) Y 0 1 Φ c' g) := by
        filter_upwards [hnb c hc g hcg] with c' hc'
        exact hTop c' hc'.1 hc'.2
      rw [vcq_pbOp_loc _ hev, vcq_pbOp_neg, hTop c hc hcg]
      have hpc := hP Wp Wq k r z z' π π' Dc Φ hz hz' hO hFam ⟨r - 1, by omega⟩ Y 0 1 c hc g hg hcg
      simp only [Q.crd] at hpc
      rw [hpc, eΨ10 hm, eΨ11 hm]
      have e2 : Q.QL k r z z' (Fin.last r) Y 0 1 (Y • Φ - Q.crd (pbOp ⟨r - 1, by omega⟩) Φ) c g =
          Y • Q.QL k r z z' (Fin.last r) Y 0 1 Φ c g +
            (-1 : ℂ) • Q.QL k r z z' (Fin.last r) Y 0 1 (Q.crd (pbOp ⟨r - 1, by omega⟩) Φ) c g := by
        show Q.tL k r z z' (Fin.last r) Y 0 1 (fun x => Y • Φ c x - Q.crd (pbOp ⟨r - 1, by omega⟩) Φ c x) g = _
        have e3 : (fun x => Y • Φ c x - Q.crd (pbOp ⟨r - 1, by omega⟩) Φ c x) =
            (fun x => Y • Φ c x + (-1 : ℂ) • Q.crd (pbOp ⟨r - 1, by omega⟩) Φ c x) := by
          funext x; rw [neg_one_smul, sub_eq_add_neg]
        rw [e3, hlin 0 1 c hc (fun x => Y • Φ c x) (Q.crd (pbOp ⟨r - 1, by omega⟩) Φ c) (-1)
          ((cq_smul hFam Y).2 c hc).1 ((cq_opL hz hz' hO hFam _ 3).2 c hc).1 g hg hcg, hsm]
        rfl
      have e4 : Q.QL k r z z' (Fin.last r) Y 1 1 (Q.crd (cbiOp ⟨r - 1, by omega⟩) Φ) c g =
          (star (c ⟨r - 1, by omega⟩))⁻¹ • Q.QL k r z z' (Fin.last r) Y 1 1 Φ c g := by
        show Q.tL k r z z' (Fin.last r) Y 1 1 (fun x => (star (c ⟨r - 1, by omega⟩))⁻¹ • Φ c x) g = _
        rw [hsm]
        rfl
      rw [e2, e4]
      simp only [cbiOp]
      module
    · have hm' : m + 2 ≤ r := hm
      have h := hS Wp Wq k r z z' π π' D Y hz hz' hD J hJ (r - (m + 2)) (by omega) c hc g hg hcg
      have e1 : (⟨r - (m + 2) + 1, by omega⟩ : Fin (r + 1)) = ⟨r - (m + 1), by omega⟩ := Fin.ext (by simp; omega)
      have e2 : (⟨r - (m + 2) + 2, by omega⟩ : Fin (r + 1)) = ⟨r - m, by omega⟩ := Fin.ext (by simp; omega)
      have e1' : (⟨r - (m + 2) + 1, by omega⟩ : Fin r) = ⟨r - (m + 1), by omega⟩ := Fin.ext (by simp; omega)
      rw [e1, e2, e1'] at h
      have e0 : (⟨r - (m + 1 + 1), by omega⟩ : Fin (r + 1)) = ⟨r - (m + 2), by omega⟩ := rfl
      rw [e0, h]
      simp only [Pi.sub_apply, Pi.smul_apply, Q.crd, cbOp, cbiOp]
      have ih1 := ih (m + 1) (by omega) (by omega)
      have ih0 := ih m (by omega) (by omega)
      have hF0 := famΨ (m + 1) (by omega) 0
      have hF1 := famΨ (m + 1) (by omega) 1
      have hev : (fun c' => FNv k r z z' Y J ⟨r - (m + 1), by omega⟩ c' g) =ᶠ[nhds c]
          (fun c' => -(Q.QL k r z z' (Fin.last r) Y 0 1 (Ψ (m + 1) 0) c' g +
            Q.QL k r z z' (Fin.last r) Y 1 1 (Ψ (m + 1) 1) c' g)) := by
        filter_upwards [hnb c hc g hcg] with c' hc'
        exact ih1 c' hc'.1 g hg hc'.2
      rw [vcq_pbOp_loc _ hev, vcq_pbOp_neg_add _ (hdiff _ (hQLfam _ hF0 0 1) c hc g hg hcg)
        (hdiff _ (hQLfam _ hF1 1 1) c hc g hg hcg)]
      have hp0 := hP Wp Wq k r z z' π π' Dc (Ψ (m + 1) 0) hz hz' hO hF0 ⟨r - (m + 2), by omega⟩ Y 0 1 c hc g hg hcg
      have hp1 := hP Wp Wq k r z z' π π' Dc (Ψ (m + 1) 1) hz hz' hO hF1 ⟨r - (m + 2), by omega⟩ Y 1 1 c hc g hg hcg
      simp only [Q.crd] at hp0 hp1
      rw [hp0, hp1, ih1 c hc g hg hcg, ih0 c hc g hg hcg]
      have hR : ∀ a : Fin 2, Q.QL k r z z' (Fin.last r) Y a 1 (Ψ (m + 2) a) c g =
          (Y • Q.QL k r z z' (Fin.last r) Y a 1 (Ψ (m + 1) a) c g +
            (-1 : ℂ) • Q.QL k r z z' (Fin.last r) Y a 1 (Q.crd (pbOp ⟨r - (m + 2), by omega⟩) (Ψ (m + 1) a)) c g) +
          (-(star (c ⟨r - (m + 1), by omega⟩) * (star (c ⟨r - (m + 2), by omega⟩))⁻¹)) •
            Q.QL k r z z' (Fin.last r) Y a 1 (Ψ m a) c g := by
        intro a
        have hA' := famΨ (m + 1) (by omega) a
        have hB' := famΨ m (by omega) a
        have hPA := cq_opL hz hz' hO hA' ⟨r - (m + 2), by omega⟩ 3
        show Q.tL k r z z' (Fin.last r) Y a 1 (Ψ (m + 2) a c) g = _
        have e5 : Ψ (m + 2) a c = fun x => (Y • Ψ (m + 1) a c x +
            (-1 : ℂ) • Q.crd (pbOp ⟨r - (m + 2), by omega⟩) (Ψ (m + 1) a) c x) +
            (-(star (c ⟨r - (m + 1), by omega⟩) * (star (c ⟨r - (m + 2), by omega⟩))⁻¹)) • Ψ m a c x := by
          rw [eΨ2 m hm' a]
          funext x
          simp only [Pi.sub_apply, Pi.smul_apply, Q.crd, cbOp, cbiOp]
          module
        rw [e5, hlin a 1 c hc (fun x => Y • Ψ (m + 1) a c x +
            (-1 : ℂ) • Q.crd (pbOp ⟨r - (m + 2), by omega⟩) (Ψ (m + 1) a) c x)
          (Ψ m a c) _ ((cq_add (cq_smul hA' Y) (cq_smul hPA (-1))).2 c hc).1 (hB'.2 c hc).1 g hg hcg,
          hlin a 1 c hc (fun x => Y • Ψ (m + 1) a c x) (Q.crd (pbOp ⟨r - (m + 2), by omega⟩) (Ψ (m + 1) a) c) (-1)
            ((cq_smul hA' Y).2 c hc).1 (hPA.2 c hc).1 g hg hcg, hsm]
        rfl
      rw [hR 0, hR 1]
      module

  have famV : ∀ i, i ≤ r → ∀ F : Q.Fn k r (Wq →L[ℂ] Wp), Q.FamFF k r z z' π π' (Fin.last r) Dc F →
      Q.FamFF k r z z' π π' (Fin.last r) Dc (Q.crd (Q.vABs r Y i).1 F) ∧
        Q.FamFF k r z z' π π' (Fin.last r) Dc (Q.crd (Q.vABs r Y i).2 F) := by
    intro i
    induction i with
    | zero =>
      intro _ F hF
      refine ⟨?_, ?_⟩
      · have e : Q.crd (Q.vABs r Y 0).1 F = F := by funext c g; rfl
        rw [e]; exact hF
      · have e : Q.crd (Q.vABs r Y 0).2 F = (0 : ℂ) • F := by funext c g; simp [Q.vABs, Q.crd]
        rw [e]; exact cq_smul hF 0
    | succ i ih =>
      intro hi F hF
      have hlt : i < r := by omega
      refine ⟨?_, ?_⟩
      · have e : Q.crd (Q.vABs r Y (i + 1)).1 F = Q.crd (Q.vABs r Y i).1 (Y • F - Q.crd (pbOp ⟨i, hlt⟩) F) -
            Q.crd (Q.vABs r Y i).2 (Q.crd (cbOp ⟨i, hlt⟩) F) := by
          funext c g; simp only [Q.vABs, dif_pos hlt, Q.crd, Pi.sub_apply]; rfl
        rw [e]
        exact cq_sub (ih (by omega) _ (cq_sub (cq_smul hF Y) (cq_opL hz hz' hO hF _ 3))).1
          (ih (by omega) _ (cq_opL hz hz' hO hF _ 4)).2
      · have e : Q.crd (Q.vABs r Y (i + 1)).2 F = Q.crd (Q.vABs r Y i).1 (Q.crd (cbiOp ⟨i, hlt⟩) F) := by
          funext c g; simp only [Q.vABs, dif_pos hlt, Q.crd]
        rw [e]
        exact (ih (by omega) _ (cq_opL hz hz' hO hF _ 5)).1
  have famVb : ∀ a : Fin 2, Q.FamFF k r z z' π π' (Fin.last r) Dc (Q.crd (Q.cmp (Q.vABs r Y r) a) Φ) := by
    intro a
    fin_cases a
    · exact (famV r le_rfl Φ hFam).1
    · exact (famV r le_rfl Φ hFam).2
  intro c hc g hg hcg
  have hk := key r le_rfl c hc g hg hcg
  have e : (⟨r - r, by omega⟩ : Fin (r + 1)) = 0 := Fin.ext (by simp)
  rw [e] at hk
  rw [hk]
  have hsw : ∀ a : Fin 2, Q.QL k r z z' (Fin.last r) Y a 1 (Ψ r a) c g =
      Q.QL k r z z' (Fin.last r) Y a 1 (Q.crd (Q.cmp (Q.vABs r Y r) a) Φ) c g := by
    intro a
    refine (Formalism.FourierDecayAlt.P.transfer_linear_local (Wq →L[ℂ] Wp) k r z z' (Fin.last r) (Dc c) Y a 1 (Ψ r a c)
      (Q.crd (Q.cmp (Q.vABs r Y r) a) Φ c) 0 (cq_isDom hD hc).1 ((famΨ r le_rfl a).2 c hc).1
      ((famVb a).2 c hc).1 g ⟨hg, hcg⟩).2 ?_
    intro x hx
    have hOx : IsOpen {c' : Fin r → ℂ | c' ∈ OmX r ∧ x ∈ Dc c'} :=
      hO.preimage (continuous_id.prodMk continuous_const)
    have hsmooth : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun c' => Φ c' x) {c' | c' ∈ OmX r ∧ x ∈ Dc c'} :=
      fun c' hc' => (cq_contDiffAt hFam.1 hc' hx.1).contDiffWithinAt
    exact hC (Wq →L[ℂ] Wp) r Y _ hOx (fun c' hc' => hc'.1) (fun c' => Φ c' x) hsmooth c ⟨hc, hx.2⟩ a
  simp only [Pi.add_apply]
  rw [hsw 0, hsw 1]

end

end Formalism.FourierDecayAlt.P.CutMP
