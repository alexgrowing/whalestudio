import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolSprayApply
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
open Filter Topology Matrix
open scoped ContDiff

set_option autoImplicit false

noncomputable section

open ReciprocityTheory.L2DbarEstimates

namespace GlobalTheory.ChernReg

variable {d : ℕ}

theorem eventually_differentiableAt_iteratedDeriv_of_contDiffAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {u : ℝ → E} {t₀ : ℝ} (hu : ContDiffAt ℝ ∞ u t₀) (i : ℕ) :
    ∀ᶠ t in 𝓝 t₀, DifferentiableAt ℝ (iteratedDeriv i u) t := by
  have h1 : ContDiffAt ℝ ((i + 1 : ℕ) : ℕ∞) u t₀ := hu.of_le (by exact_mod_cast le_top)
  filter_upwards [h1.eventually (by simp)] with t ht
  have h2 : ContDiffAt ℝ 1 (iteratedFDeriv ℝ i u) t :=
    ht.iteratedFDeriv_right (by push_cast; exact (add_comm _ _).le)
  have h3 := h2.differentiableAt one_ne_zero
  have e : iteratedDeriv i u = fun x => iteratedFDeriv ℝ i u x (fun _ => 1) :=
    funext fun x => iteratedDeriv_eq_iteratedFDeriv
  rw [e]
  exact h3.continuousMultilinear_apply_const _

theorem iteratedDeriv_eq_of_eventuallyEq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : ℝ → E} {t₀ : ℝ} (h : f =ᶠ[𝓝 t₀] g) (n : ℕ) : iteratedDeriv n f t₀ = iteratedDeriv n g t₀ := by
  rw [← iteratedDerivWithin_univ, ← iteratedDerivWithin_univ]
  exact Filter.EventuallyEq.iteratedDerivWithin_eq (by rwa [nhdsWithin_univ]) h.eq_of_nhds

theorem holSpray_eventuallyEq {b : V d → Matrix (Fin d) (Fin d) ℂ} {f f' : V d × V d → V d}
    {q : V d × V d} (h : f =ᶠ[𝓝 q] f') : holSpray b f =ᶠ[𝓝 q] holSpray b f' := by
  filter_upwards [h.eventuallyEq_nhds] with q' hq'
  simp only [holSpray_apply, GlobalTheory.del_congr hq']

theorem iterate_holSpray_eventuallyEq {b : V d → Matrix (Fin d) (Fin d) ℂ} {q : V d × V d} (n : ℕ) :
    ∀ {f f' : V d × V d → V d}, f =ᶠ[𝓝 q] f' → (holSpray b)^[n] f =ᶠ[𝓝 q] (holSpray b)^[n] f' := by
  induction n with
  | zero => intro f f' h; exact h
  | succ n ih =>
    intro f f' h
    simp only [Function.iterate_succ_apply]
    exact ih (holSpray_eventuallyEq h)

theorem holSpray_comp_jets (b : V d → Matrix (Fin d) (Fin d) ℂ) {m : ℕ} {G : (Fin (m + 1) → V d) → V d}
    {q : V d × V d} (hJ : DifferentiableAt ℝ (fun q => fun i : Fin (m + 1) => jet b i q) q)
    (hG : DifferentiableAt ℂ G (fun i : Fin (m + 1) => jet b i q)) :
    holSpray b (fun q => G (fun i : Fin (m + 1) => jet b i q)) q =
      fderiv ℂ G (fun i : Fin (m + 1) => jet b i q) (fun i : Fin (m + 1) => jet b (i + 1) q) := by
  rw [holSpray_apply, GlobalTheory.del_comp (hG.restrictScalars ℝ) hJ, GlobalTheory.dbar_eq_zero hG,
    GlobalTheory.del_eq_fderiv hG, ContinuousLinearMap.zero_apply, add_zero]
  congr 1
  funext i
  have := GlobalTheory.del_clm_comp (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (m + 1) => V d) i) hJ
    (q.2, -christoffel b q.1 q.2)
  exact this.symm

theorem hasDerivAt_comp_derivs {u : ℝ → V d} {m : ℕ} {G : (Fin (m + 1) → V d) → V d} {t : ℝ}
    (hd : ∀ i : Fin (m + 1), DifferentiableAt ℝ (iteratedDeriv i u) t)
    (hG : DifferentiableAt ℂ G (fun i : Fin (m + 1) => iteratedDeriv i u t)) :
    HasDerivAt (fun t => G (fun i : Fin (m + 1) => iteratedDeriv i u t))
      (fderiv ℂ G (fun i : Fin (m + 1) => iteratedDeriv i u t)
        (fun i : Fin (m + 1) => iteratedDeriv (i + 1) u t)) t := by
  have hc : HasDerivAt (fun t => fun i : Fin (m + 1) => iteratedDeriv i u t)
      (fun i : Fin (m + 1) => iteratedDeriv (i + 1) u t) t :=
    hasDerivAt_pi.2 fun i => by rw [iteratedDeriv_succ]; exact (hd i).hasDerivAt
  exact (hG.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t hc

def jetsDeriv {m : ℕ} (G : (Fin (m + 1) → V d) → V d) (x : Fin (m + 2) → V d) : V d :=
  fderiv ℂ G (fun i : Fin (m + 1) => x i.castSucc) (fun i : Fin (m + 1) => x i.succ)

theorem differentiableOn_jetsDeriv {m : ℕ} {G : (Fin (m + 1) → V d) → V d} {W : Set (Fin (m + 1) → V d)}
    (hW : IsOpen W) (hG : DifferentiableOn ℂ G W) :
    DifferentiableOn ℂ (jetsDeriv G) {x | (fun i : Fin (m + 1) => x i.castSucc) ∈ W} := by
  intro x hx
  have hp : Differentiable ℂ (fun x : Fin (m + 2) → V d => fun i : Fin (m + 1) => x i.castSucc) :=
    differentiable_pi.2 fun i => differentiable_apply _
  have hs : Differentiable ℂ (fun x : Fin (m + 2) → V d => fun i : Fin (m + 1) => x i.succ) :=
    differentiable_pi.2 fun i => differentiable_apply _
  have hf := ((GlobalTheory.SCV.differentiableOn_fderiv hW hG) _ hx).differentiableAt (hW.mem_nhds hx)
  exact ((hf.comp x (hp x)).clm_apply (hs x)).differentiableWithinAt

variable {U : Set (V d)} {b : V d → Matrix (Fin d) (Fin d) ℂ} {z ξ : V d} {u : ℝ → V d}

theorem iteratedDeriv_comp_derivs (hU : IsOpen U)
    (hJ : ∀ n, ContDiffOn ℝ ∞ (jet b n) (U ×ˢ (Set.univ : Set (V d)))) (hz : z ∈ U)
    (hu : ContDiffAt ℝ ∞ u 0) (hu0 : ∀ n, iteratedDeriv n u 0 = jet b n (z, ξ)) (n : ℕ) :
    ∀ (m : ℕ) (W : Set (Fin (m + 1) → V d)) (G : (Fin (m + 1) → V d) → V d), IsOpen W →
      DifferentiableOn ℂ G W → (fun i : Fin (m + 1) => jet b i (z, ξ)) ∈ W →
      iteratedDeriv n (fun t => G (fun i : Fin (m + 1) => iteratedDeriv i u t)) 0 =
        (holSpray b)^[n] (fun q => G (fun i : Fin (m + 1) => jet b i q)) (z, ξ) := by
  induction n with
  | zero =>
    intro m W G _ _ _
    simp only [iteratedDeriv_zero, Function.iterate_zero, id, hu0]
  | succ n ih =>
    intro m W G hW hG hmem
    have hJd : ∀ i, ∀ q ∈ U ×ˢ (Set.univ : Set (V d)), DifferentiableAt ℝ (jet b i) q := fun i q hq =>
      ((hJ i).contDiffAt ((hU.prod isOpen_univ).mem_nhds hq)).differentiableAt (by simp)
    have hJm : ∀ q ∈ U ×ˢ (Set.univ : Set (V d)),
        DifferentiableAt ℝ (fun q => fun i : Fin (m + 1) => jet b i q) q := fun q hq =>
      differentiableAt_pi.2 fun i => hJd i q hq
    have hzq : (z, ξ) ∈ U ×ˢ (Set.univ : Set (V d)) := ⟨hz, trivial⟩

    have hdu : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ i : Fin (m + 2), DifferentiableAt ℝ (iteratedDeriv i u) t :=
      Filter.eventually_all.2 fun i => eventually_differentiableAt_iteratedDeriv_of_contDiffAt hu i
    have hcW : ∀ᶠ t in 𝓝 (0 : ℝ), (fun i : Fin (m + 1) => iteratedDeriv i u t) ∈ W := by
      have hc : ContinuousAt (fun t => fun i : Fin (m + 1) => iteratedDeriv i u t) 0 :=
        continuousAt_pi.2 fun i => (hdu.self_of_nhds i.castSucc).continuousAt
      refine hc.preimage_mem_nhds (hW.mem_nhds ?_)
      simpa only [hu0] using hmem
    have hL : deriv (fun t => G (fun i : Fin (m + 1) => iteratedDeriv i u t)) =ᶠ[𝓝 0]
        fun t => jetsDeriv G (fun i : Fin (m + 2) => iteratedDeriv i u t) := by
      filter_upwards [hdu, hcW] with t ht htW
      exact (hasDerivAt_comp_derivs (fun i => ht i.castSucc)
        (hG.differentiableAt (hW.mem_nhds htW))).deriv

    have hJW : ∀ᶠ q in 𝓝 (z, ξ), (fun i : Fin (m + 1) => jet b i q) ∈ W :=
      (hJm _ hzq).continuousAt.preimage_mem_nhds (hW.mem_nhds hmem)
    have hR : holSpray b (fun q => G (fun i : Fin (m + 1) => jet b i q)) =ᶠ[𝓝 (z, ξ)]
        fun q => jetsDeriv G (fun i : Fin (m + 2) => jet b i q) := by
      filter_upwards [(hU.prod isOpen_univ).mem_nhds hzq, hJW] with q hq hqW
      exact holSpray_comp_jets b (hJm q hq) (hG.differentiableAt (hW.mem_nhds hqW))
    rw [iteratedDeriv_succ', iteratedDeriv_eq_of_eventuallyEq hL, Function.iterate_succ_apply,
      (iterate_holSpray_eventuallyEq n hR).eq_of_nhds]
    exact ih (m + 1) _ (jetsDeriv G) (hW.preimage (f := fun x : Fin (m + 2) → V d => fun i : Fin (m + 1) => x i.castSucc)
        (continuous_pi fun i => continuous_apply _))
      (differentiableOn_jetsDeriv hW hG) hmem

theorem iteratedDeriv_comp_eq_iterate_holSpray (d : ℕ) (U : Set (V d)) (b : V d → Matrix (Fin d) (Fin d) ℂ)
    (g : V d → V d) (hU : IsOpen U)
    (hJ : ∀ n, ContDiffOn ℝ ∞ (GlobalTheory.ChernReg.jet b n) (U ×ˢ (Set.univ : Set (V d))))
    (hg : DifferentiableOn ℂ g U) : ∀ z ∈ U, ∀ (ξ : V d) (u : ℝ → V d), ContDiffAt ℝ ∞ u 0 →
      (∀ n, iteratedDeriv n u 0 = GlobalTheory.ChernReg.jet b n (z, ξ)) → ∀ (n : ℕ),
      iteratedDeriv n (g ∘ u) 0 = (GlobalTheory.ChernReg.holSpray b)^[n] (g ∘ Prod.fst) (z, ξ) := by
  intro z hz ξ u hu hu0 n
  have hG : DifferentiableOn ℂ (fun x : Fin 1 → V d => g (x 0)) {x | x 0 ∈ U} :=
    hg.comp (differentiable_apply 0).differentiableOn fun _ hx => hx
  have h := iteratedDeriv_comp_derivs hU hJ hz hu hu0 n 0 {x | x 0 ∈ U} _
    (hU.preimage (continuous_apply 0)) hG hz
  simpa only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, iteratedDeriv_zero, jet_zero, Function.comp_def,
    Fin.isValue, Fin.val_zero] using h

end GlobalTheory.ChernReg
