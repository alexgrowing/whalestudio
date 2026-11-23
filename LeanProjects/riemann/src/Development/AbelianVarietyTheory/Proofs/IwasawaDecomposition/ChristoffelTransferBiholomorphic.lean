import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolSprayApply
import ReciprocityTheory.SemistableReduction.ShareDetA
open Filter Topology Matrix
open scoped ContDiff

set_option autoImplicit false

noncomputable section

open ReciprocityTheory.L2DbarEstimates

namespace GlobalTheory.ChernReg

theorem holSpray_iterate_comp (d : ℕ) (U U' : Set (V d)) (τ : V d → V d)
    (b b' : V d → Matrix (Fin d) (Fin d) ℂ) (hU : IsOpen U) (hU' : IsOpen U') (hτ : DifferentiableOn ℂ τ U)
    (hmap : Set.MapsTo τ U U')
    (hjet : ∀ n, ContDiffOn ℝ ∞ (jet b' n) (U' ×ˢ (Set.univ : Set (V d))))
    (htr : ∀ z ∈ U, ∀ ξ : V d, fderiv ℂ τ z (christoffel b z ξ) =
      christoffel b' (τ z) (fderiv ℂ τ z ξ) + fderiv ℂ (fderiv ℂ τ) z ξ ξ) :
    ∀ (n : ℕ), ∀ q ∈ U ×ˢ (Set.univ : Set (V d)),
      (holSpray b)^[n] (τ ∘ Prod.fst) q = jet b' n (τ q.1, fderiv ℂ τ q.1 q.2) := by
  have hA : AnalyticOnNhd ℂ τ U := by
    intro z hz
    let e : V d ≃L[ℂ] (Fin d → ℂ) := EuclideanSpace.equiv (Fin d) ℂ
    have hc : ∀ i, AnalyticAt ℂ (fun v => e (τ v) i) z := fun i =>
      ReciprocityTheory.MultiplicativeHeights.analyticOnNhd_V_of_differentiableOn hU
        (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin d => ℂ) i).comp
          (e : V d →L[ℂ] (Fin d → ℂ))).differentiable.comp_differentiableOn hτ) z hz
    have hp : AnalyticAt ℂ (fun v => e (τ v)) z := analyticAt_pi_iff.2 hc
    have h : AnalyticAt ℂ (fun v => e.symm (e (τ v))) z :=
      ((e.symm : (Fin d → ℂ) →L[ℂ] V d).analyticAt _).comp hp
    convert h using 1
    funext v
    simp
  have hO : IsOpen (U ×ˢ (Set.univ : Set (V d))) := hU.prod isOpen_univ
  have hO' : IsOpen (U' ×ˢ (Set.univ : Set (V d))) := hU'.prod isOpen_univ

  have hT : ∀ q ∈ U ×ˢ (Set.univ : Set (V d)), HasFDerivAt (𝕜 := ℂ)
      (fun x : V d × V d => (τ x.1, fderiv ℂ τ x.1 x.2))
      (((fderiv ℂ τ q.1).comp (ContinuousLinearMap.fst ℂ (V d) (V d))).prod
        ((fderiv ℂ τ q.1).comp (ContinuousLinearMap.snd ℂ (V d) (V d)) +
          ((fderiv ℂ (fderiv ℂ τ) q.1).comp (ContinuousLinearMap.fst ℂ (V d) (V d))).flip q.2)) q := by
    intro q hq
    have h1 : HasFDerivAt (fun x : V d × V d => τ x.1)
        ((fderiv ℂ τ q.1).comp (ContinuousLinearMap.fst ℂ (V d) (V d))) q :=
      ((hA q.1 hq.1).differentiableAt.hasFDerivAt).comp q (hasFDerivAt_fst)
    have h2 : HasFDerivAt (fun x : V d × V d => fderiv ℂ τ x.1)
        ((fderiv ℂ (fderiv ℂ τ) q.1).comp (ContinuousLinearMap.fst ℂ (V d) (V d))) q :=
      ((hA.fderiv q.1 hq.1).differentiableAt.hasFDerivAt).comp q (hasFDerivAt_fst)
    exact h1.prodMk (h2.clm_apply hasFDerivAt_snd)
  intro n
  induction n with
  | zero => intro q _; rfl
  | succ n ih =>
    intro q hq
    rw [Function.iterate_succ_apply', holSpray_apply]
    have hev : (holSpray b)^[n] (τ ∘ Prod.fst) =ᶠ[𝓝 q]
        (fun x : V d × V d => jet b' n (τ x.1, fderiv ℂ τ x.1 x.2)) :=
      Filter.eventually_of_mem (hO.mem_nhds hq) ih
    have hTq : (τ q.1, fderiv ℂ τ q.1 q.2) ∈ U' ×ˢ (Set.univ : Set (V d)) := ⟨hmap hq.1, trivial⟩
    have hd : DifferentiableAt ℝ (jet b' n) (τ q.1, fderiv ℂ τ q.1 q.2) :=
      ((hjet n).contDiffAt (hO'.mem_nhds hTq)).differentiableAt (by simp)
    rw [del_congr hev, del_comp_holo (φ := fun x : V d × V d => (τ x.1, fderiv ℂ τ x.1 x.2)) hd
      (hT q hq).differentiableAt, (hT q hq).fderiv, jet_succ]
    congr 1
    have h := htr q.1 hq.1 q.2
    simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', ContinuousLinearMap.add_apply, ContinuousLinearMap.flip_apply, map_neg, h,
      Prod.mk.injEq, true_and]
    abel

end GlobalTheory.ChernReg
