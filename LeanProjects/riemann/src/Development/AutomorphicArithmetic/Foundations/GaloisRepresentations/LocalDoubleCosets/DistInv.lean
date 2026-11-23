import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.TracePow

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL ValuativeRel Matrix MeasureTheory UpperTheory.ConvolutionTheory.Loc MulAction UpperTheory.Gal.LocD

private theorem comp_mem_Cc {X : Type} [TopologicalSpace X] (s : X → X) (q : ℕ) (hs : Continuous s)
    (hsp : ∀ x, s^[q + 1] x = x) {f : X → ℂ} (hf : f ∈ Cc X) : f ∘ s ∈ Cc X := by
  obtain ⟨h1, h2⟩ := hf
  let e : X ≃ₜ X :=
    { toFun := s
      invFun := s^[q]
      left_inv := fun y => by
        show s^[q] (s y) = y
        rw [← Function.iterate_succ_apply s q y, hsp]
      right_inv := fun y => by
        show s (s^[q] y) = y
        rw [← Function.iterate_succ_apply' s q y, hsp]
      continuous_toFun := hs
      continuous_invFun := hs.iterate q }
  exact ⟨h1.comp_continuous hs, h2.comp_homeomorph e⟩

theorem UpperTheory.Gal.LocD.distInv :
    DistZero → DistInv := by
  intro hZ X H _ _ _ _ _ _ _ _ _ _ _ _ _ s τ p hp hs hτ hsp hτp hsτ χ hχL hχτ k x hxs horb hcl D hD f hf
  have hsp' : ∀ y, s^[p - 1 + 1] y = y := fun y => by rw [Nat.sub_add_cancel hp]; exact hsp y
  have cc : ∀ g ∈ Cc X, g ∘ s ∈ Cc X := fun g hg => comp_mem_Cc s (p - 1) hs hsp' hg
  let D' : (X → ℂ) →ₗ[ℂ] ℂ := D.comp (LinearMap.funLeft ℂ ℂ s) - D
  have hD'apply : ∀ g, D' g = D (g ∘ s) - D g := fun g => rfl
  have key := hZ X H s τ p hp hs hτ hsp hτp hsτ χ hχL k x hxs horb hcl D' ?_ ?_ f hf
  · rw [hD'apply, sub_eq_zero] at key
    exact key
  · intro h g hg
    rw [hD'apply, hD'apply]
    set h' := τ^[p - 1] h with hh'
    have hτh : τ h' = h := by
      rw [hh', ← Function.iterate_succ_apply' τ (p - 1) h, Nat.succ_eq_add_one,
        Nat.sub_add_cancel hp, hτp]
    have hχh : χ h' = χ h := by rw [← hχτ h', hτh]
    have hcomp : GroundTheory.Automorphic.Whittaker.transl h g ∘ s
        = GroundTheory.Automorphic.Whittaker.transl h' (g ∘ s) := by
      ext y
      simp only [Function.comp_apply, GroundTheory.Automorphic.Whittaker.transl_apply]
      rw [hsτ, map_inv, hτh]
    rw [hcomp, hD h' _ (cc g hg), hD h g hg, hχh]
    ring
  · intro g hg
    have h1 : ∀ i, D' (g ∘ s^[i]) = D (g ∘ s^[i + 1]) - D (g ∘ s^[i]) := fun i => rfl
    simp only [h1]
    rw [Finset.sum_range_sub (fun i => D (g ∘ s^[i]))]
    have hid : s^[p] = id := funext hsp
    simp [hid]
