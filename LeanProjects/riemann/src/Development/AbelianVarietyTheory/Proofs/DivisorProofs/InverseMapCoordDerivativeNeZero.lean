import Mathlib

open scoped ContDiff Topology
open Filter

namespace GlobalTheory

theorem localBiholom_partial_ne_zero_of_vanishing :
    ∀ {e : ℕ} (T S : (Fin e → ℂ) → (Fin e → ℂ)) (z0 : Fin e → ℂ) (j k : Fin e),
      DifferentiableAt ℂ T z0 → DifferentiableAt ℂ S (T z0) → S (T z0) = z0 →
      (∀ᶠ w in 𝓝 (T z0), T (S w) = w) → z0 k = 0 →
      (∀ᶠ z in 𝓝 z0, z k = 0 → T z j = 0) →
      fderiv ℂ (fun z => T z j) z0 (Pi.single k 1) ≠ 0 := by
  intro e T S z0 j k hT hS hST hTS hk hvan
  set A := fderiv ℂ T z0 with hA
  set B := fderiv ℂ S (T z0) with hB
  have hT' : HasFDerivAt T A z0 := hT.hasFDerivAt
  have hS' : HasFDerivAt S B (T z0) := hS.hasFDerivAt
  have hT'' : HasFDerivAt T A (S (T z0)) := by rw [hST]; exact hT'
  have hcomp : HasFDerivAt (T ∘ S) (A.comp B) (T z0) := hT''.comp (T z0) hS'
  have hid : HasFDerivAt (T ∘ S) (ContinuousLinearMap.id ℂ (Fin e → ℂ)) (T z0) :=
    (hasFDerivAt_id (T z0)).congr_of_eventuallyEq (by
      filter_upwards [hTS] with w hw
      simp [hw])
  have hAB : A.comp B = ContinuousLinearMap.id ℂ (Fin e → ℂ) := hcomp.unique hid

  have hj : HasFDerivAt (fun z => T z j) ((ContinuousLinearMap.proj j).comp A) z0 :=
    (hasFDerivAt_pi'.mp hT') j
  have hℓ : fderiv ℂ (fun z => T z j) z0 = (ContinuousLinearMap.proj j).comp A := hj.fderiv
  rw [hℓ]
  set ℓ : (Fin e → ℂ) →L[ℂ] ℂ := (ContinuousLinearMap.proj j).comp A with hℓdef

  have hne : ℓ (B (Pi.single j 1)) = 1 := by
    have := congrArg (fun L : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ) => L (Pi.single j 1)) hAB
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at this
    simp [hℓdef, this]

  have hother : ∀ l, l ≠ k → ℓ (Pi.single l 1) = 0 := by
    intro l hl
    set v : Fin e → ℂ := Pi.single l 1
    have hline : HasDerivAt (fun t : ℂ => z0 + t • v) v 0 := by
      simpa using ((hasDerivAt_id (0:ℂ)).smul_const v).const_add z0
    have h0 : (fun t : ℂ => z0 + t • v) 0 = z0 := by simp
    have hj0 : HasFDerivAt (fun z => T z j) ℓ ((fun t : ℂ => z0 + t • v) 0) := by rw [h0]; exact hj
    have hg : HasDerivAt (fun t : ℂ => T (z0 + t • v) j) (ℓ v) 0 := by
      have := HasFDerivAt.comp_hasDerivAt (l := fun z => T z j) (0:ℂ) hj0 hline
      exact this
    have htend : Tendsto (fun t : ℂ => z0 + t • v) (𝓝 0) (𝓝 z0) := by
      have := hline.continuousAt.tendsto
      simpa using this
    have hev : (fun t : ℂ => T (z0 + t • v) j) =ᶠ[𝓝 0] fun _ => (0:ℂ) := by
      filter_upwards [htend.eventually hvan] with t ht
      apply ht
      simp [v, Pi.single_apply, Ne.symm hl, hk]
    have hg0 : HasDerivAt (fun t : ℂ => T (z0 + t • v) j) 0 0 :=
      (hasDerivAt_const (0:ℂ) (0:ℂ)).congr_of_eventuallyEq hev
    exact hg.unique hg0
  intro hkz
  have hzero : ℓ = 0 := by
    have hlin : (ℓ : (Fin e → ℂ) →ₗ[ℂ] ℂ) = 0 := by
      apply LinearMap.pi_ext
      intro i x
      have hsx : (Pi.single i x : Fin e → ℂ) = x • Pi.single i 1 := by
        rw [← Pi.single_smul]; simp
      rw [hsx, map_smul, LinearMap.zero_apply]
      by_cases hik : i = k
      · subst hik; simp [hkz]
      · simp [hother i hik]
    ext1 v
    exact congrArg (fun L : (Fin e → ℂ) →ₗ[ℂ] ℂ => L v) hlin
  rw [hzero] at hne
  simp at hne

end GlobalTheory
