import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.IdLiftDef

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open NumberField

theorem l_theta : IntegralTraceSurjective := by
  intro E _ _ _ h
  obtain ⟨_, _, hun⟩ := h
  let σ : 𝓞 E →+* 𝓞 E := RingOfIntegers.mapRingHom (starRingEnd E)
  have hσ : ∀ x : 𝓞 E, ((σ x : 𝓞 E) : E) = star (x : E) := fun x => rfl
  have hσσ : ∀ x, σ (σ x) = x := fun x => RingOfIntegers.ext (by rw [hσ, hσ, star_star])
  let J : Ideal (𝓞 E) := Ideal.span {t | ∃ x, t = x + σ x}
  have hJ : J = ⊤ := by
    by_contra hne
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal J hne
    obtain ⟨θ, t, ht, hnot⟩ := hun P hP
    have htσ : t = σ θ := RingOfIntegers.ext (by rw [hσ]; exact ht)
    apply hnot
    have h1 : θ + σ θ ∈ P := hle (Ideal.subset_span ⟨θ, rfl⟩)
    have h2 : (1 : 𝓞 E) + σ 1 ∈ P := hle (Ideal.subset_span ⟨1, rfl⟩)
    rw [map_one] at h2
    have h3 : θ - t = (θ + σ θ) - (1 + 1) * σ θ := by rw [htσ]; ring
    rw [h3]
    exact P.sub_mem h1 (P.mul_mem_right _ h2)
  have key : ∀ y ∈ J, ∃ x, y * σ y = x + σ x := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨x, rfl⟩ := ht
      exact ⟨(x + σ x) * x, by simp only [map_add, map_mul, hσσ]; ring⟩
    | zero => exact ⟨0, by simp⟩
    | add y y' _ _ ih ih' =>
      obtain ⟨x, hx⟩ := ih
      obtain ⟨x', hx'⟩ := ih'
      exact ⟨x + x' + y * σ y', by simp only [map_add, map_mul, hσσ]; linear_combination hx + hx'⟩
    | smul a y _ ih =>
      obtain ⟨x, hx⟩ := ih
      exact ⟨a * σ a * x, by simp only [smul_eq_mul, map_mul, hσσ]; linear_combination (a * σ a) * hx⟩
  obtain ⟨x, hx⟩ := key 1 (by rw [hJ]; exact Submodule.mem_top)
  refine ⟨x, ?_⟩
  rw [map_one, mul_one] at hx
  have h4 := congrArg (fun z : 𝓞 E => (z : E)) hx
  simp only [map_add, map_one] at h4
  rw [← hσ]
  exact h4.symm

end Formalism.MainNotions.BridgeLemma

end
