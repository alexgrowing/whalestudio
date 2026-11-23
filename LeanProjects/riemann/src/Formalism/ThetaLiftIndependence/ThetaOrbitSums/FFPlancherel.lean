import Formalism.ThetaLiftIndependence.Statement

namespace Formalism.ThetaLiftIndependence

namespace FiniteFieldPlancherel

open Classical

theorem charSum {𝔽 U : Type} [Field 𝔽] [AddCommGroup U] [Module 𝔽 U] [Fintype U]
    (ψ : AddChar 𝔽 ℂ) (hψ : ψ ≠ 1) (g : Module.Dual 𝔽 U) :
    ∑ e : U, ψ (g e) = if g = 0 then (Fintype.card U : ℂ) else 0 := by
  by_cases hg : g = 0
  · subst hg; simp
  · rw [if_neg hg]
    obtain ⟨a, ha⟩ : ∃ a, ψ a ≠ 1 := by
      by_contra h
      push Not at h
      apply hψ
      ext a
      simp [h a]
    obtain ⟨x, hx⟩ : ∃ x, g x ≠ 0 := by
      by_contra h
      push Not at h
      exact hg (LinearMap.ext fun x => by simp [h x])
    set e0 : U := (a / g x) • x with he0
    have hge0 : g e0 = a := by
      rw [he0, map_smul, smul_eq_mul, div_mul_cancel₀ _ hx]
    have hshift : ∑ e : U, ψ (g e) = (∑ e : U, ψ (g e)) * ψ a := by
      calc ∑ e : U, ψ (g e) = ∑ e : U, ψ (g (e + e0)) :=
            (Fintype.sum_equiv (Equiv.addRight e0) _ _ (fun _ => rfl)).symm
        _ = (∑ e : U, ψ (g e)) * ψ a := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun e _ => ?_
            rw [map_add, AddChar.map_add_eq_mul, hge0]
    have h1 : (∑ e : U, ψ (g e)) * (ψ a - 1) = 0 := by
      rw [mul_sub, mul_one, ← hshift, sub_self]
    rcases mul_eq_zero.mp h1 with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp h) ha

theorem orth {𝔽 U : Type} [Field 𝔽] [AddCommGroup U] [Module 𝔽 U] [Fintype U]
    (ψ : AddChar 𝔽 ℂ) (hψ : ψ ≠ 1) [Fintype 𝔽] (f g : Module.Dual 𝔽 U) :
    ∑ e : U, star (ψ (f e)) * ψ (g e) = if f = g then (Fintype.card U : ℂ) else 0 := by
  have h : ∀ e, star (ψ (f e)) * ψ (g e) = ψ ((g - f) e) := by
    intro e
    rw [LinearMap.sub_apply, sub_eq_add_neg, AddChar.map_add_eq_mul, AddChar.map_neg_eq_conj,
      Complex.star_def, mul_comm]
  simp_rw [h]
  rw [charSum ψ hψ]
  by_cases hfg : f = g
  · simp [hfg]
  · rw [if_neg hfg, if_neg (fun h' => hfg (sub_eq_zero.mp h').symm)]

end FiniteFieldPlancherel
