import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec

set_option autoImplicit false

open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace Filter Topology

namespace GlobalTheory.AnPer.Charts

theorem exists_glue_fn {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F)
    (hK : K.Rich) (a : ∀ k, Hol (K.W k)) (ha : ∀ k k' (e : K.le 0 k' k), sh e (a k) = a k') :
    ∃ G : Tot I g → ℂ, ∀ k, ∀ q ∈ K.W k, G q = (a k).fn q := by
  classical
  have key : ∀ k₁ k₂ q, q ∈ K.W k₁ → q ∈ K.W k₂ → (a k₁).fn q = (a k₂).fn q := by
    intro k₁ k₂ q h₁ h₂
    obtain ⟨k, hk, e₁, e₂⟩ := hK.2 0 k₁ k₂ q h₁ (by rw [F.shift_zero]; exact h₂)
    have r₁ := fn_sh e₁ (a k₁) hk
    have r₂ := fn_sh e₂ (a k₂) hk
    rw [ha, F.shift_zero] at r₁ r₂
    rw [← r₁, ← r₂]
  refine ⟨fun q ↦ if h : ∃ k, q ∈ K.W k then (a h.choose).fn q else 0, fun k q hq ↦ ?_⟩
  have h : ∃ k, q ∈ K.W k := ⟨k, hq⟩
  simp only [dif_pos h]
  exact key _ _ q h.choose_spec hq

theorem exists_cst_of_dw_eq_zero : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ}
    (K : Charts F), K.Rich → ∀ (a : ∀ k, Hol (K.W k)), (∀ k k' (e : K.le 0 k' k), sh e (a k) = a k') →
    (∀ k i, dw i (a k) = 0) → ∃ p : Hol F.V, ∀ k, a k = K.cst k p := by
  intro I _ g Λ _ F K hK a ha hd
  obtain ⟨G, hG⟩ := exists_glue_fn K hK a ha
  have ev : ∀ k, ∀ q ∈ K.W k, G =ᶠ[𝓝 q] (a k).fn := fun k q hq ↦ by
    filter_upwards [(K.W k).isOpen.mem_nhds hq] with r hr using hG k r hr
  have an : ∀ q : Tot I g, q.1 ∈ F.V → AnalyticAt ℂ G q := fun q hq ↦ by
    obtain ⟨k, hk⟩ := hK.1 q hq
    exact ((a k).analytic q hk).congr (ev k q hk).symm
  have d0 : ∀ q : Tot I g, q.1 ∈ F.V → ∀ i, fderiv ℂ G q ((0, Pi.single i 1) : Tot I g) = 0 := fun q hq i ↦ by
    obtain ⟨k, hk⟩ := hK.1 q hq
    rw [(ev k q hk).fderiv_eq, ← Hol.fn_der _ _ hk]
    change (dw i (a k)).fn q = 0
    rw [hd, ← Hol.ev_apply q hk, map_zero]
  have cs : ∀ z ∈ F.V, ∀ w, G (z, w) = G (z, 0) := fun z hz w ↦ by
    have hf : ∀ w : Fin g → ℂ, HasFDerivAt (fun w ↦ G (z, w))
        ((fderiv ℂ G (z, w)).comp (ContinuousLinearMap.inr ℂ (I → ℂ) (Fin g → ℂ))) w := fun w ↦
      (an (z, w) hz).differentiableAt.hasFDerivAt.comp w (hasFDerivAt_prodMk_right z w)
    refine is_const_of_fderiv_eq_zero (𝕜 := ℂ) (f := fun w ↦ G (z, w)) (fun w ↦ (hf w).differentiableAt)
      (fun w ↦ ?_) w 0
    rw [(hf w).fderiv]
    ext v
    have hv : ((0, v) : Tot I g) = ∑ i, v i • ((0, Pi.single i 1) : Tot I g) := by
      ext j
      · simp [Prod.fst_sum]
      · simp [Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
    change fderiv ℂ G (z, w) (0, v) = 0
    rw [hv, map_sum]
    exact Finset.sum_eq_zero fun i _ ↦ by rw [map_smul, d0 (z, w) hz i, smul_zero]
  refine ⟨Hol.mk (fun z ↦ G (z, 0)) fun z hz ↦
    AnalyticAt.comp (g := G) (f := fun z ↦ ((z, 0) : Tot I g)) (an (z, 0) hz)
      (analyticAt_id.prod analyticAt_const), fun k ↦ Hol.ext_fn fun q hq ↦ ?_⟩
  rw [fn_cst _ _ _ hq, ← hG k q hq]
  exact (cs q.1 (K.base k q hq) q.2).trans (Hol.fn_mk (fun z ↦ G (z, 0)) _ (K.base k q hq)).symm

end GlobalTheory.AnPer.Charts
