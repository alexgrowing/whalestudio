import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.UnitHmD

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.UH

open NumberField ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Complex ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H}

theorem relab_injective (c : Coeff l) (σ : c.F →+* ℂ) : Function.Injective (relab c σ) := by
  intro a b h
  ext x
  have h1 : σ (embF c a x) = σ (embF c b x) := congrArg (fun f : E →+* ℂ => f x) h
  have h2 := σ.injective h1
  exact congrArg Subtype.val h2

theorem relab_rt (c : Coeff l) (σ : c.F →+* ℂ) (hσ : GoodEmb c σ) (τ : E →+* ℂ) :
    relab c σ τ (H.rt : E) = H.rt0 ↔ τ (H.rt : E) = H.rt0 := by
  have e1 : (H.rt : E) ^ 2 = -(H.d : E) := by
    have h := congrArg (fun x : 𝓞 E => (x : E)) H.rt_sq
    simpa using h
  have hsq : τ (H.rt : E) ^ 2 = H.rt0 ^ 2 := by
    rw [← map_pow, e1, map_neg, map_natCast, H.sqrt_neg_disc_sq]
  have hcases : τ (H.rt : E) = H.rt0 ∨ τ (H.rt : E) = -H.rt0 := sq_eq_sq_iff_eq_or_eq_neg.mp hsq
  have hg : σ ((IntermediateField.inclusion c.le) (baseKA l).ρ) = H.rt0 := hσ
  unfold relab
  rw [RingHom.comp_apply]
  rcases hcases with h | h
  · have hy : embF c τ (H.rt : E) = (IntermediateField.inclusion c.le) (baseKA l).ρ := Subtype.ext h
    rw [hy, hg, h]
  · have hy : embF c τ (H.rt : E) = -(IntermediateField.inclusion c.le) (baseKA l).ρ := Subtype.ext h
    rw [hy, map_neg, hg, h]

theorem letter_sum (c : Coeff l) (σ : c.F →+* ℂ) (hσ : GoodEmb c σ) (Dw : Datum H) {g : ℕ}
    (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (Ψ : Finset (E →+* ℂ))
    (hΨ : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ τ (H.rt : E) = H.rt0)
    (hcm : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ conjEmb τ ∉ Ψ) (G : (E →+* ℂ) → ℕ → ℝ) :
    ∑ j : Fin g, G (relab c σ (e j).1) (e j).2 =
      ∑ τ ∈ Ψ, ((∑ n ∈ Finset.range Dw.p, G τ n) + ∑ n ∈ Finset.range Dw.q, G (conjEmb τ) n) := by
  classical
  have hrel : ∀ τ : E →+* ℂ, Dw.mult τ = if relab c σ τ ∈ Ψ then Dw.p else Dw.q := by
    intro τ
    unfold Datum.mult
    by_cases h : τ (H.rt : E) = H.rt0
    · rw [if_pos h, if_pos ((hΨ _).mpr ((relab_rt c σ hσ τ).mpr h))]
    · rw [if_neg h, if_neg (fun h' => h ((relab_rt c σ hσ τ).mp ((hΨ _).mp h')))]
  have hinv : ∀ τ : E →+* ℂ, conjEmb (conjEmb τ) = τ := fun τ => RingHom.ext fun x => by simp [conjEmb]
  rw [Equiv.sum_comp e (fun x => G (relab c σ x.1) x.2), Fintype.sum_sigma]
  rw [Finset.sum_congr rfl (fun τ _ => Fin.sum_univ_eq_sum_range (G (relab c σ τ)) (Dw.mult τ))]
  rw [Fintype.sum_bijective (relab c σ) (relab_injective c σ).bijective_of_finite
      (fun τ => ∑ n ∈ Finset.range (Dw.mult τ), G (relab c σ τ) n)
      (fun τ' => ∑ n ∈ Finset.range (if τ' ∈ Ψ then Dw.p else Dw.q), G τ' n)
      (fun τ => by rw [hrel τ])]
  rw [← Finset.sum_add_sum_compl Ψ, Finset.sum_add_distrib]
  congr 1
  · exact Finset.sum_congr rfl (fun τ hτ => by rw [if_pos hτ])
  · refine Finset.sum_nbij' conjEmb conjEmb ?_ ?_ ?_ ?_ ?_
    · intro a ha
      exact (hcm (conjEmb a)).mpr (by rw [hinv]; exact Finset.mem_compl.mp ha)
    · intro a ha
      exact Finset.mem_compl.mpr ((hcm a).mp ha)
    · intro a _
      exact hinv a
    · intro a _
      exact hinv a
    · intro a ha
      rw [if_neg (Finset.mem_compl.mp ha), hinv]

end ReciprocityTheory.ChartRestriction.G.PullbackSections.UH
