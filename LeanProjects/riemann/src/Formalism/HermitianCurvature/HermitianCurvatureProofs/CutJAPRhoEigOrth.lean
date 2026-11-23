import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRhoCut

open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.PRhoCut

open Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

namespace EigenvectorOrthogonality

variable {k r : ℕ}

private theorem herm_mulVec_of_conjTranspose_mul_H_mul_eq {n : ℕ} {H g : Matrix (Fin n) (Fin n) ℂ} (hg : gᴴ * H * g = H)
    (v w : Fin n → ℂ) : herm H (g *ᵥ v) (g *ᵥ w) = herm H v w := by
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
  simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hg]

theorem frame_move {z e : Fin (2 * r + k + 1) → ℂ} {h : Mx k r} (hh : h ∈ UWset k r z) (he : h *ᵥ e = e) {m : ℕ}
    {F : Fin m → Fin (2 * r + k + 1) → ℂ} (hF : IsFrameOf k r [z, e] F) :
    IsFrameOf k r [z, e] (fun p => h *ᵥ F p) := by
  have hG : h ∈ Glev k r (Fin.last r) := ⟨hh.1, fun a _ => hh.2.1 a⟩
  have hU : hᴴ * Hpk k r * h = Hpk k r := hh.1
  refine ⟨fun a => (Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.glev_inWb hG (hF.1 a)).1, fun a b => ?_, fun a v hv => ?_⟩
  · rw [herm_mulVec_of_conjTranspose_mul_H_mul_eq hU]
    exact hF.2.1 a b
  · have hv' : h *ᵥ v = v := by
      rcases List.mem_cons.1 hv with rfl | hv2
      · exact hh.2.2
      · rcases List.mem_cons.1 hv2 with rfl | hv3
        · exact he
        · simp at hv3
    calc herm (Hpk k r) (h *ᵥ F a) v = herm (Hpk k r) (h *ᵥ F a) (h *ᵥ v) := by rw [hv']
      _ = 0 := by rw [herm_mulVec_of_conjTranspose_mul_H_mul_eq hU]; exact hF.2.2 a v hv

theorem frame_swap {z e : Fin (2 * r + k + 1) → ℂ} {m : ℕ} {F : Fin m → Fin (2 * r + k + 1) → ℂ}
    (hF : IsFrameOf k r [z, e] F) : IsFrameOf k r [e, z] F :=
  ⟨hF.1, hF.2.1, fun a v hv => hF.2.2 a v (by simp only [List.mem_cons] at hv ⊢; tauto)⟩

private theorem isUnit_det_of_mem_UWset {h : Mx k r} {z : Fin (2 * r + k + 1) → ℂ} (hh : h ∈ UWset k r z) :
    IsUnit h.det := by
  have hU : hᴴ * Hpk k r * h = Hpk k r := hh.1
  have hH : (Hpk k r).det ≠ 0 := by
    have h1 := congrArg Matrix.det (Formalism.QuantumDeterminants.hpkFacts k r).2.1
    rw [Matrix.det_mul, Matrix.det_one] at h1
    intro h0
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  have h2 := congrArg Matrix.det hU
  rw [Matrix.det_mul, Matrix.det_mul] at h2
  refine isUnit_iff_ne_zero.2 fun h0 => hH ?_
  rw [h0, mul_zero] at h2
  exact h2.symm

theorem mulVec_inv_cancel {h : Mx k r} {z : Fin (2 * r + k + 1) → ℂ} (hh : h ∈ UWset k r z) (v : Fin (2 * r + k + 1) → ℂ) :
    h *ᵥ (h⁻¹ *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_det_of_mem_UWset hh), Matrix.one_mulVec]

theorem inv_fix {h : Mx k r} {z e : Fin (2 * r + k + 1) → ℂ} (hh : h ∈ UWset k r z) (he : h *ᵥ e = e) :
    h⁻¹ *ᵥ e = e := by
  calc h⁻¹ *ᵥ e = h⁻¹ *ᵥ (h *ᵥ e) := by rw [he]
    _ = e := by rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_det_of_mem_UWset hh), Matrix.one_mulVec]

end EigenvectorOrthogonality

open EigenvectorOrthogonality in
theorem eigenvector_orthogonality_holds : EigOrth := by
  intro Wp _ _ _ k r z e π hz hT hrep hunit hex f g x y hx hy hfg
  obtain ⟨Fr₀, hFr₀⟩ := hex
  obtain ⟨w₀, hw₀⟩ := hfg
  have hlin : ∀ Fr : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ, IsFrameOf k r [z, e] Fr → ∀ w,
      P.Qx8.IsLin (capRep k r π Fr w) := fun Fr hFr w =>
    P.Qx8.capRep_lin hFr (by simp) hrep.1 hrep.2 w
  set S := K k r z e π g with hS

  have hmem : ∀ v ∈ S, v ∈ Kset k r z e π g := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem u hu => exact hu
    | zero =>
      intro Fr hFr w
      rw [(hlin Fr hFr w).map_zero, smul_zero]
    | add a b _ _ ha hb =>
      intro Fr hFr w
      rw [(hlin Fr hFr w).map_add, ha Fr hFr w, hb Fr hFr w, smul_add]
    | smul c a _ ha =>
      intro Fr hFr w
      rw [(hlin Fr hFr w).map_smul, ha Fr hFr w, smul_comm]

  have hmul : ∀ a ∈ UWset k r z, ∀ b ∈ UWset k r z, ∀ v, π (a * b) v = π a (π b v) := by
    intro a ha b hb v
    rw [hrep.1.2 a ha b hb]; rfl
  have hinv : ∀ h ∈ UWset k r z, ∀ v, π h (π h⁻¹ v) = v := by
    intro h hh v
    rw [← hmul h hh _ (WeylGroupFacts.uw_inv hh), Matrix.mul_nonsing_inv _ (WeylGroupFacts.isUnit_of_uh hh.1), hrep.1.1]; rfl
  have hstab : ∀ h ∈ UWset k r z, h *ᵥ e = e → ∀ v ∈ Kset k r z e π g, π h v ∈ Kset k r z e π g := by
    intro h hh he v hv Fr hFr w
    have hFr' : IsFrameOf k r [z, e] (fun p => h⁻¹ *ᵥ Fr p) := frame_move (WeylGroupFacts.uw_inv hh) (inv_fix hh he) hFr
    have key := P.Qx8.capRep_intertwine (frame_swap hFr') hrep.1 hrep.2 hh.1 (π h)
      (fun h' hh' _ v => by
        rw [← hmul h hh h' hh', ← hmul _ (WeylGroupFacts.uw_mul (WeylGroupFacts.uw_mul hh hh') (WeylGroupFacts.uw_inv hh)) h hh,
          Matrix.mul_assoc (h * h'), Matrix.nonsing_inv_mul _ (WeylGroupFacts.isUnit_of_uh hh.1), Matrix.mul_one]) w v
    simp only [mulVec_inv_cancel hh] at key
    rw [← key, hv _ hFr' w, map_smul]
  have hstabS : ∀ h ∈ UWset k r z, h *ᵥ e = e → ∀ v ∈ S, π h v ∈ S := fun h hh he v hv =>
    Submodule.subset_span (hstab h hh he v (hmem v hv))
  have hstabO : ∀ h ∈ UWset k r z, h *ᵥ e = e → ∀ u ∈ Sᗮ, π h u ∈ Sᗮ := by
    intro h hh he u hu s hs
    let L : Wp →ₗᵢ[ℂ] Wp := ⟨(π h : Wp →ₗ[ℂ] Wp), hunit h hh⟩
    have hs' : π h⁻¹ s ∈ S := hstabS _ (WeylGroupFacts.uw_inv hh) (inv_fix hh he) s hs
    have e2 : inner ℂ (π h (π h⁻¹ s)) (π h u) = inner ℂ (π h⁻¹ s) u := L.inner_map_map _ _
    rw [hinv h hh s] at e2
    rw [e2]
    exact Submodule.inner_right_of_mem_orthogonal hs' hu
  have hcomm : ∀ h ∈ UWset k r z, h *ᵥ e = e → ∀ v, S.starProjection (π h v) = π h (S.starProjection v) := by
    intro h hh he v
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (hstabS h hh he _ (S.starProjection_apply_mem v)) ?_
    intro s hs
    have : π h v - π h (S.starProjection v) = π h (v - S.starProjection v) := by rw [map_sub]
    rw [this]
    exact Submodule.inner_left_of_mem_orthogonal hs
      (hstabO h hh he _ (Submodule.sub_starProjection_mem_orthogonal v))
  have hcap : ∀ v, S.starProjection (capRep k r π Fr₀ w₀ v) = capRep k r π Fr₀ w₀ (S.starProjection v) := by
    intro v
    have key := P.Qx8.capRep_intertwine (frame_swap hFr₀) hrep.1 hrep.2 WeylGroupFacts.uh_one
      (S.starProjection : Wp →L[ℂ] Wp) (fun h' hh' he' v => by
        rw [inv_one, Matrix.one_mul, Matrix.mul_one]; exact hcomm h' hh' he' v) w₀ v
    simpa only [Matrix.one_mulVec] using key
  have hAx : S.starProjection x = 0 := by
    have h1 := hmem _ (S.starProjection_apply_mem x) Fr₀ hFr₀ w₀
    rw [← hcap, hx Fr₀ hFr₀ w₀, map_smul] at h1
    have h2 : (f w₀ - g w₀) • S.starProjection x = 0 := by rw [sub_smul, h1, sub_self]
    exact (smul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hw₀)
  have hyS : y ∈ S := Submodule.subset_span hy
  rw [← (Submodule.starProjection_eq_self_iff).2 hyS, ← Submodule.inner_starProjection_left_eq_right, hAx, inner_zero_left]

end Formalism.FourierDecayAlt.P.CutMP.JA.PRhoCut
