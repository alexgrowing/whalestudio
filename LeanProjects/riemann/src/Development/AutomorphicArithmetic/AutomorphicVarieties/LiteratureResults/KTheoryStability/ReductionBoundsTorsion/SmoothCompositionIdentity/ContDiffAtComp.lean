import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.BasicForm

noncomputable section

open Filter Topology ContinuousAlternatingMap
open scoped ContDiff

namespace PositivityTheory.KB.TwAG

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {q : ℕ}

theorem exists_clm (f : V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] V) : ∃ B : V →L[ℝ] V →L[ℝ] V →L[ℝ] V, ∀ a b c, B a b c = f a b c := by
  let L1 : (V →ₗ[ℝ] V) →ₗ[ℝ] (V →L[ℝ] V) := LinearMap.toContinuousLinearMap.toLinearMap
  let L2 : (V →ₗ[ℝ] (V →L[ℝ] V)) →ₗ[ℝ] (V →L[ℝ] V →L[ℝ] V) := LinearMap.toContinuousLinearMap.toLinearMap
  exact ⟨LinearMap.toContinuousLinearMap (L2 ∘ₗ f.compr₂ L1), fun a b c => rfl⟩

theorem contDiffAt_comp {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {α : X → V [⋀^Fin q]→L[ℝ] ℝ}
    {A : X → V →L[ℝ] V} {x : X} (β : V [⋀^Fin q]→L[ℝ] ℝ) (hA : ContDiffAt ℝ ∞ A x) :
    ContDiffAt ℝ ∞ (fun y => β.compContinuousLinearMap (A y)) x := by
  have hdiff : ContDiff ℝ ∞ (fun B : V →L[ℝ] V => β.compContinuousLinearMap B) := by
    let M := ContinuousMultilinearMap ℝ (fun _ : Fin q => V) ℝ
    haveI : FiniteDimensional ℝ M := Module.Finite.of_injective
      (ContinuousMultilinearMap.toMultilinearMapLinear (R' := ℝ) (A := ℝ) :
        M →ₗ[ℝ] MultilinearMap ℝ (fun _ : Fin q => V) ℝ)
      ContinuousMultilinearMap.toMultilinearMap_injective
    let ι : (V [⋀^Fin q]→L[ℝ] ℝ) →ₗ[ℝ] M :=
      (ContinuousAlternatingMap.toContinuousMultilinearMapCLM (𝕜 := ℝ) ℝ).toLinearMap
    have hι : LinearMap.ker ι = ⊥ :=
      LinearMap.ker_eq_bot.2 ContinuousAlternatingMap.toContinuousMultilinearMap_injective
    obtain ⟨g, hg⟩ := ι.exists_leftInverse_of_injective hι
    let G : M →L[ℝ] (V [⋀^Fin q]→L[ℝ] ℝ) := ⟨g, LinearMap.continuous_of_finiteDimensional g⟩
    have key : (fun B : V →L[ℝ] V => β.compContinuousLinearMap B) = fun B =>
        G (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ
          (fun _ : Fin q => V) (fun _ : Fin q => V) ℝ (fun _ => B) β.toContinuousMultilinearMap) := by
      funext B
      rw [ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear_apply_apply]
      exact (LinearMap.congr_fun hg (β.compContinuousLinearMap B)).symm
    rw [key]
    have hd : ContDiff ℝ ∞ (fun B : V →L[ℝ] V => fun _ : Fin q => B) :=
      contDiff_pi.2 fun _ => contDiff_id
    have h1 : ContDiff ℝ ∞ (fun B : V →L[ℝ] V =>
        ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ
          (fun _ : Fin q => V) (fun _ : Fin q => V) ℝ (fun _ => B)) :=
      (ContinuousMultilinearMap.contDiff _).comp hd
    have h2 := (ContinuousLinearMap.apply ℝ M β.toContinuousMultilinearMap).contDiff.comp h1
    exact G.contDiff.comp h2
  exact hdiff.contDiffAt.comp x hA

theorem core (B : V →L[ℝ] V →L[ℝ] V →L[ℝ] V) (e : V) (h1 : B e e = 1)
    (hsym : ∀ x y, B e x y + B x e y = B e y x + B y e x) (he : ∀ y, B e y e + B y e e = (2 : ℝ) • y)
    (o : V → V [⋀^Fin q]→L[ℝ] ℝ) (ho : ∀ᶠ x in 𝓝 e, (o (B x x e)).compContinuousLinearMap (B x x) = o e) :
    ContDiffAt ℝ ∞ o e ∧ extDeriv o e = 0 := by
  have hQ : ∀ x, HasFDerivAt (fun y => B y y) (B.flip x + B x) x := by
    intro x
    have := B.hasFDerivAt_of_bilinear (hasFDerivAt_id x) (hasFDerivAt_id x)
    refine this.congr_fderiv ?_
    ext w u
    simp [add_comm]
  have hQs : ContDiff ℝ ∞ (fun y => B y y) := B.contDiff.clm_apply contDiff_id
  have hφs : ContDiff ℝ ∞ (fun y => B y y e) := hQs.clm_apply contDiff_const
  let L : V ≃L[ℝ] V := (LinearEquiv.smulOfNeZero ℝ V 2 two_ne_zero).toContinuousLinearEquiv
  have hLw : ∀ w, (L : V →L[ℝ] V) w = (2 : ℝ) • w := fun w => rfl
  have hφe : HasFDerivAt (fun y => B y y e) (L : V →L[ℝ] V) e := by
    have h0 : HasFDerivAt (fun y => B y y e) ((ContinuousLinearMap.apply ℝ V e).comp (B.flip e + B e)) e :=
      (ContinuousLinearMap.apply ℝ V e).hasFDerivAt.comp e (hQ e)
    convert h0 using 1
    ext w
    rw [hLw, ← he w]
    simp [add_comm]
  have hee : B e e e = e := by rw [h1]; rfl
  have hstrict : HasStrictFDerivAt (fun y => B y y e) (L : V →L[ℝ] V) e :=
    hφs.contDiffAt.hasStrictFDerivAt' hφe (by simp)
  have hψ : ContDiffAt ℝ ∞ (hstrict.localInverse _ _ _) (B e e e) :=
    hφs.contDiffAt.to_localInverse hφe (by simp)
  have hright := hstrict.eventually_right_inverse
  have htend := hstrict.localInverse_tendsto
  have himg := hstrict.localInverse_apply_image
  rw [hee] at hright htend himg hψ
  have hP : ContDiffAt ℝ ∞ (fun y => B (hstrict.localInverse _ _ _ y) (hstrict.localInverse _ _ _ y)) e :=
    hQs.contDiffAt.comp e hψ
  have hPe : B (hstrict.localInverse _ _ _ e) (hstrict.localInverse _ _ _ e) = 1 := by
    rw [himg, h1]
  have hunit : ∀ᶠ y in 𝓝 e, IsUnit (B (hstrict.localInverse _ _ _ y) (hstrict.localInverse _ _ _ y)) := by
    have hm : {x : V →L[ℝ] V | IsUnit x} ∈ 𝓝 (B (hstrict.localInverse _ _ _ e) (hstrict.localInverse _ _ _ e)) :=
      Units.isOpen.mem_nhds (by rw [hPe]; exact isUnit_one)
    exact hP.continuousAt.preimage_mem_nhds hm
  have hid : ∀ᶠ y in 𝓝 e, (o y).compContinuousLinearMap
      (B (hstrict.localInverse _ _ _ y) (hstrict.localInverse _ _ _ y)) = o e := by
    filter_upwards [htend.eventually ho, hright] with y hy1 hy2
    rw [hy2] at hy1
    exact hy1
  have hrep : o =ᶠ[𝓝 e] fun y => (o e).compContinuousLinearMap
      (Ring.inverse (B (hstrict.localInverse _ _ _ y) (hstrict.localInverse _ _ _ y))) := by
    filter_upwards [hid, hunit] with y hy hu
    rw [← hy]
    ext v
    simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
    congr 1
    funext i
    simp only [Function.comp_apply]
    rw [← ContinuousLinearMap.mul_apply, Ring.mul_inverse_cancel _ hu]
    rfl
  have hsm : ContDiffAt ℝ ∞ o e := by
    have hR : ContDiffAt ℝ ∞
        (fun y => Ring.inverse (B (hstrict.localInverse _ _ _ y) (hstrict.localInverse _ _ _ y))) e := by
      refine ContDiffAt.comp (g := Ring.inverse) e ?_ hP
      rw [hPe]
      simpa using contDiffAt_ringInverse (𝕜 := ℝ) (n := ∞) (1 : (V →L[ℝ] V)ˣ)
    exact (contDiffAt_comp (α := o) (o e) hR).congr_of_eventuallyEq hrep
  refine ⟨hsm, ?_⟩
  have hdo : HasFDerivAt o (fderiv ℝ o e) e := (hsm.differentiableAt (by simp)).hasFDerivAt
  have hG1 : HasFDerivAt (fun x => (o (B x x e)).compContinuousLinearMap (B x x))
      ((ContinuousAlternatingMap.compContinuousLinearMapCLM (B e e)) ∘L (fderiv ℝ o e ∘L (L : V →L[ℝ] V)) +
        (o (B e e e)).fderivCompContinuousLinearMap (B e e) ∘L (B.flip e + B e)) e := by
    have h2 : HasFDerivAt (fun x => o (B x x e)) (fderiv ℝ o e ∘L (L : V →L[ℝ] V)) e := by
      have h3 : HasFDerivAt o (fderiv ℝ o e) (B e e e) := by rw [hee]; exact hdo
      exact HasFDerivAt.comp (g := o) (f := fun y => B y y e) e h3 hφe
    exact h2.continuousAlternatingMapCompContinuousLinearMap (hQ e)
  have hG2 : HasFDerivAt (fun x => (o (B x x e)).compContinuousLinearMap (B x x))
      (0 : V →L[ℝ] (V [⋀^Fin q]→L[ℝ] ℝ)) e :=
    (hasFDerivAt_const (o e) e).congr_of_eventuallyEq ho
  have huniq := hG1.unique hG2
  have hcomp1 : ∀ T : V [⋀^Fin q]→L[ℝ] ℝ,
      ContinuousAlternatingMap.compContinuousLinearMapCLM (1 : V →L[ℝ] V) T = T := by
    intro T
    ext v
    rfl
  have hDw : ∀ w, fderiv ℝ o e w = (o e).fderivCompContinuousLinearMap 1
      (((-(1/2 : ℝ)) • (B.flip e + B e)) w) := by
    intro w
    have hw := congrArg (fun T => T w) huniq
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.zero_apply] at hw
    rw [hee, h1, hcomp1, hLw, map_smul] at hw
    have hX := eq_neg_of_add_eq_zero_right hw
    rw [ContinuousLinearMap.smul_apply, map_smul, ContinuousLinearMap.add_apply, hX, smul_neg, smul_smul]
    first | norm_num | simp
  have hfd : fderiv ℝ o e = (o e).fderivCompContinuousLinearMap 1 ∘L
      ((-(1/2 : ℝ)) • (B.flip e + B e)) := by
    ext1 w
    exact hDw w
  rw [extDeriv, hfd]
  apply ContinuousAlternatingMap.alternatizeUncurryFin_fderivCompContinuousLinearMap_eq_zero
  intro x y
  have hs := hsym x y
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.flip_apply]
  rw [add_comm (B x e y), hs, add_comm]

theorem transport (A : V →L[ℝ] V) {h : V} (o : V → V [⋀^Fin q]→L[ℝ] ℝ) (hc : ContDiffAt ℝ ∞ o (A h))
    (h0 : extDeriv o (A h) = 0) (ho : ∀ᶠ x in 𝓝 h, (o (A x)).compContinuousLinearMap A = o x) :
    ContDiffAt ℝ ∞ o h ∧ extDeriv o h = 0 := by
  have hfd : ∀ x, fderiv ℝ (⇑A) x = A := fun x => A.fderiv
  have heq : (fun x => (o (A x)).compContinuousLinearMap (fderiv ℝ (⇑A) x)) =ᶠ[𝓝 h] o := by
    filter_upwards [ho] with x hx
    rw [hfd]
    exact hx
  have hcA : ContDiffAt ℝ ∞ (fun x => o (A x)) h := hc.comp h A.contDiff.contDiffAt
  have hsm : ContDiffAt ℝ ∞ (fun x => (o (A x)).compContinuousLinearMap (fderiv ℝ (⇑A) x)) h := by
    simp only [hfd]
    exact (ContinuousAlternatingMap.compContinuousLinearMapCLM A).contDiff.contDiffAt.comp h hcA
  refine ⟨hsm.congr_of_eventuallyEq heq.symm, ?_⟩
  rw [← heq.extDeriv_eq, extDeriv_pullback (r := ∞) (hc.differentiableAt (by simp))
    A.contDiff.contDiffAt
    (by simp; exact ENat.LEInfty.out), h0]
  ext v
  simp

end PositivityTheory.KB.TwAG

end
