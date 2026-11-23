import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods
import Development.AbelianVarietyTheory.Definitions.ThetaValues.MemAnalyticAtZeroOfEventuallyDifferentiableAt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ConstantCoeffDpolyOfAdditiveTaylorPts
open Filter Topology

namespace GlobalTheory

open Filter Topology in
private lemma iteratedFDeriv_slice_eq_compContinuousLinearMap_inl {E F : Type} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] (H : E × F → ℂ) {w : F}
    (hH : AnalyticAt ℂ H (0, w)) (k : ℕ) :
    iteratedFDeriv ℂ k (fun z ↦ H (z, w)) 0 =
      (iteratedFDeriv ℂ k H (0, w)).compContinuousLinearMap
        (fun _ ↦ ContinuousLinearMap.inl ℂ E F) := by
  obtain ⟨U, hU, hUo, hwU⟩ := eventually_nhds_iff.1 hH.eventually_analyticAt
  set s : Set (E × F) := (fun q ↦ q + (0, w)) ⁻¹' U with hs
  have hso : IsOpen s := hUo.preimage (continuous_id.add continuous_const)
  have h0s : (0 : E × F) ∈ s := by simpa [hs] using hwU
  have hf : AnalyticOnNhd ℂ (fun q : E × F ↦ H (q + (0, w))) s := fun q hq ↦
    (hU _ hq).comp (f := fun q : E × F ↦ q + (0, w)) (analyticAt_id.add analyticAt_const)
  have hslice : (fun z : E ↦ H (z, w)) =
      (fun q : E × F ↦ H (q + (0, w))) ∘ ContinuousLinearMap.inl ℂ E F := by
    ext z; simp
  have hpre : IsOpen (ContinuousLinearMap.inl ℂ E F ⁻¹' s) :=
    hso.preimage (ContinuousLinearMap.continuous _)
  have h0s' : ContinuousLinearMap.inl ℂ E F 0 ∈ s := by rw [map_zero]; exact h0s
  have h0pre : (0 : E) ∈ ContinuousLinearMap.inl ℂ E F ⁻¹' s := h0s'
  rw [hslice, ← iteratedFDerivWithin_of_isOpen k hpre h0pre,
    ContinuousLinearMap.iteratedFDerivWithin_comp_right _ (hf.contDiffOn (n := k) hso.uniqueDiffOn)
      hso.uniqueDiffOn hpre.uniqueDiffOn h0s' le_rfl,
    iteratedFDerivWithin_of_isOpen k hso h0s', iteratedFDeriv_comp_add_right]
  simp

open Filter Topology in
private lemma fin_snoc_eq_cons_comp_finRotate {X : Type} {k : ℕ} (u : Fin k → X) (a : X) :
    (Fin.snoc u a : Fin (k + 1) → X) = Fin.cons a u ∘ finRotate (k + 1) := by
  funext i
  refine Fin.lastCases ?_ (fun i ↦ ?_) i
  · simp
  · simp

open Filter Topology in

theorem _root_.GlobalTheory.analyticAt_iteratedFDeriv_slice_and_fderiv :
    ∀ {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] (H : E × F → ℂ) (w₀ : F) (k : ℕ) (v : Fin k → E), AnalyticAt ℂ H (0, w₀) → AnalyticAt ℂ (fun w ↦ iteratedFDeriv ℂ k (fun z ↦ H (z, w)) 0 v) w₀ ∧ ∀ e : F, fderiv ℂ (fun w ↦ iteratedFDeriv ℂ k (fun z ↦ H (z, w)) 0 v) w₀ e = iteratedFDeriv ℂ k (fun z ↦ fderiv ℂ H (z, w₀) (0, e)) 0 v := by
  intro E F _ _ _ _ _ _ H w₀ k v hH
  set u : Fin k → E × F := fun i ↦ (v i, 0) with hu
  have hev : ∀ᶠ w in 𝓝 w₀, AnalyticAt ℂ H (0, w) :=
    ((continuous_const.prodMk continuous_id).tendsto w₀).eventually hH.eventually_analyticAt
  have heq : (fun w ↦ iteratedFDeriv ℂ k (fun z ↦ H (z, w)) 0 v) =ᶠ[𝓝 w₀]
      fun w ↦ iteratedFDeriv ℂ k H (0, w) u :=
    hev.mono fun w hw ↦ by dsimp only; rw [iteratedFDeriv_slice_eq_compContinuousLinearMap_inl H hw k]; rfl
  obtain ⟨U, hU, hUo, hwU⟩ := eventually_nhds_iff.1 hH.eventually_analyticAt
  have hiter : AnalyticAt ℂ (iteratedFDeriv ℂ k H) (0, w₀) :=
    (AnalyticOnNhd.iteratedFDeriv_of_isOpen hU hUo k) _ hwU
  have hA : AnalyticAt ℂ (fun w ↦ iteratedFDeriv ℂ k H (0, w) u) w₀ :=
    ((ContinuousMultilinearMap.apply ℂ (fun _ : Fin k ↦ E × F) ℂ u).analyticAt _).comp
      (hiter.comp (f := fun w : F ↦ ((0 : E), w)) (analyticAt_const.prod analyticAt_id))
  refine ⟨hA.congr heq.symm, fun e ↦ ?_⟩
  have hD : HasFDerivAt (fun w ↦ iteratedFDeriv ℂ k H (0, w) u)
      ((ContinuousMultilinearMap.apply ℂ (fun _ : Fin k ↦ E × F) ℂ u).comp
        ((fderiv ℂ (iteratedFDeriv ℂ k H) (0, w₀)).comp (ContinuousLinearMap.inr ℂ E F))) w₀ :=
    (ContinuousMultilinearMap.apply ℂ (fun _ : Fin k ↦ E × F) ℂ u).hasFDerivAt.comp w₀
      (hiter.differentiableAt.hasFDerivAt.comp w₀ (hasFDerivAt_prodMk_right (0 : E) w₀))
  have hG : AnalyticAt ℂ (fun y ↦ fderiv ℂ H y (0, e)) (0, w₀) :=
    ((ContinuousLinearMap.apply ℂ ℂ ((0 : E), e)).analyticAt _).comp hH.fderiv
  rw [heq.fderiv_eq, hD.fderiv, iteratedFDeriv_slice_eq_compContinuousLinearMap_inl _ hG k]
  have hcomp : (fun y ↦ fderiv ℂ H y (0, e)) =
      (ContinuousLinearMap.apply ℂ ℂ ((0 : E), e)) ∘ fderiv ℂ H := rfl
  rw [hcomp, ContinuousLinearMap.iteratedFDeriv_comp_left _ (hH.fderiv.contDiffAt (n := k)) le_rfl]
  have hperm := (hH.contDiffAt (n := ⊤)).iteratedFDeriv_comp_perm (Fin.cons ((0 : E), e) u)
    (finRotate (k + 1))
  rw [← fin_snoc_eq_cons_comp_finRotate, iteratedFDeriv_succ_apply_right,
    iteratedFDeriv_succ_apply_left] at hperm
  simpa [u] using hperm.symm

end GlobalTheory
