import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.IntegralityGoodReduction

noncomputable section

open Matrix
open scoped ContDiff

namespace UpperTheory.V.Lit.Dr

private theorem fderiv_apply_elim0_eq_zero_of_extDeriv_eq_zero {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : V → V [⋀^Fin 0]→L[ℝ] F) (x : V)
    (hd : DifferentiableAt ℝ f x) (h : extDeriv f x = 0) :
    fderiv ℝ (fun y => f y Fin.elim0) x = 0 := by
  ext1 h'
  have := extDeriv_apply hd (fun _ : Fin 1 => h')
  rw [h, Fin.sum_univ_one] at this
  rw [Subsingleton.elim (Fin.removeNth 0 fun _ : Fin 1 => h') Fin.elim0] at this
  simpa using this.symm

theorem inclFacts : InclFacts := by
  intro Γ V S _ _ _ d G hconv hne
  obtain ⟨p0, hp0⟩ := hne
  have back : ∀ (γ : Γ) (p : V), p ∉ G.Y → (G.ρ γ⁻¹) p ∉ G.Y := by
    intro γ p hp h
    have h2 := G.maps γ _ h
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      ContinuousLinearMap.one_apply] at h2
    exact hp h2
  refine ⟨?_, ?_, ?_⟩
  · intro γ f
    apply Subtype.ext
    funext s p
    change G.Y.indicator (fun _ => ContinuousAlternatingMap.constOfIsEmpty ℝ V (Fin 0)
        (G.ξ γ *ᵥ f ((G.σ γ⁻¹) s))) p =
      G.tr 0 γ (G.Y.indicator (fun _ => ContinuousAlternatingMap.constOfIsEmpty ℝ V (Fin 0)
        (f ((G.σ γ⁻¹) s))) ((G.ρ γ⁻¹) p))
    by_cases hp : p ∈ G.Y
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem (G.maps γ⁻¹ p hp)]
      ext v i
      simp [Geo.tr]
    · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem (back γ p hp), map_zero]
  · intro f g hfg
    funext s
    have h := congrArg (fun w : G.Om 0 => (w : S → V → V [⋀^Fin 0]→L[ℝ] (Fin d → ℂ)) s p0 Fin.elim0) hfg
    simpa [Geo.incl, Set.indicator_of_mem hp0] using h
  · intro w
    constructor
    · intro hw
      have hd : ∀ s, ∀ x ∈ G.Y, extDeriv ((w : S → V → V [⋀^Fin 0]→L[ℝ] (Fin d → ℂ)) s) x = 0 := by
        intro s x hx
        have := congrArg (fun w' : G.Om 1 => (w' : S → V → V [⋀^Fin 1]→L[ℝ] (Fin d → ℂ)) s x) hw
        simpa [Geo.dOm, Set.indicator_of_mem hx] using this
      refine ⟨fun s => (w : S → V → V [⋀^Fin 0]→L[ℝ] (Fin d → ℂ)) s p0 Fin.elim0, ?_⟩
      apply Subtype.ext
      funext s p
      have hda : ∀ y ∈ G.Y, DifferentiableAt ℝ ((w : S → V → V [⋀^Fin 0]→L[ℝ] (Fin d → ℂ)) s) y := fun y hy =>
        ((w.2 s).1.contDiffAt (G.isOpen.mem_nhds hy)).differentiableAt (by simp)
      have hdiff : DifferentiableOn ℝ (fun y => (w : S → V → V [⋀^Fin 0]→L[ℝ] (Fin d → ℂ)) s y Fin.elim0) G.Y := fun y hy =>
        ((hda y hy).continuousAlternatingMap_apply_const _).differentiableWithinAt
      have hconst : ∀ y ∈ G.Y, (w : S → V → V [⋀^Fin 0]→L[ℝ] (Fin d → ℂ)) s y Fin.elim0 = (w : S → V → V [⋀^Fin 0]→L[ℝ] (Fin d → ℂ)) s p0 Fin.elim0 := fun y hy =>
        hconv.is_const_of_fderivWithin_eq_zero hdiff (fun x hx => by
          rw [fderivWithin_of_isOpen G.isOpen hx]
          exact fderiv_apply_elim0_eq_zero_of_extDeriv_eq_zero _ x (hda x hx) (hd s x hx)) hy hp0
      change G.Y.indicator (fun _ => ContinuousAlternatingMap.constOfIsEmpty ℝ V (Fin 0)
        ((w : S → V → V [⋀^Fin 0]→L[ℝ] (Fin d → ℂ)) s p0 Fin.elim0)) p = (w : S → V → V [⋀^Fin 0]→L[ℝ] (Fin d → ℂ)) s p
      by_cases hp : p ∈ G.Y
      · rw [Set.indicator_of_mem hp]
        ext v
        rw [Subsingleton.elim v Fin.elim0]
        simp [hconst p hp]
      · rw [Set.indicator_of_notMem hp, (w.2 s).2 p hp]
    · rintro ⟨f, rfl⟩
      apply Subtype.ext
      funext s p
      change G.Y.indicator (extDeriv (G.Y.indicator fun _ =>
        ContinuousAlternatingMap.constOfIsEmpty ℝ V (Fin 0) (f s))) p = 0
      by_cases hp : p ∈ G.Y
      · rw [Set.indicator_of_mem hp, Filter.EventuallyEq.extDeriv_eq
          (Filter.eventuallyEq_of_mem (G.isOpen.mem_nhds hp) (fun x hx => Set.indicator_of_mem hx _))]
        rw [extDeriv, fderiv_const_apply, ← ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply,
          map_zero]
      · rw [Set.indicator_of_notMem hp]

end UpperTheory.V.Lit.Dr
