import Formalism.SharpRestriction.GrowthBounds.RootWeights.FiltrationAdjointStable

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

def highestWeightSpace {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (E : GLOps n K V) (mu : Fin n → ℤ) :
    Submodule K V :=
  weightSp E mu ⊓ ⨅ a : Fin n, ⨅ b : Fin n, ⨅ (_ : a < b), LinearMap.ker (E a b)

theorem mem_highestWeightSpace_iff {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {E : GLOps n K V}
    {mu : Fin n → ℤ} {x : V} : x ∈ highestWeightSpace E mu ↔ x ∈ weightSp E mu ∧ ∀ a b : Fin n, a < b → E a b x = 0 := by
  simp [highestWeightSpace, Submodule.mem_iInf]

theorem weightSpace_le_hwv_sup_nMinus (D : Formalism.BasicNotions.D7) {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {n : ℕ} (E : GLOps n K V) (hE : IsGLRep E) (mu : Fin n → ℤ) :
    weightSp E mu ≤ highestWeightSpace E mu ⊔ (nMinus E ⊓ weightSp E mu) := by
  have hs := gl_rep_shifts_weights hE
  have htop := sum_isotypic_top_of_weight_data D (weight_condition_from_integral_form D) E hE hs (findim_weights_bounded E) (weight_projections_integral_findim E)
  obtain ⟨Θ, _, hΘ⟩ := weight_projections_integral_findim E
  have hle : ∀ ν, isoSub E ν ≤ (highestWeightSpace E mu ⊔ (nMinus E ⊓ weightSp E mu)).comap (Θ mu) := by
    intro ν
    refine Submodule.span_le.2 ?_
    rintro y ⟨u, hu, v, hv, rfl⟩
    have hY : loweringWordSpan E v ≤ (highestWeightSpace E mu ⊔ (nMinus E ⊓ weightSp E mu)).comap (Θ mu) := by
      refine Submodule.span_le.2 ?_
      rintro w ⟨u', hu', rfl⟩
      obtain ⟨⟨κ, hκ⟩, h⟩ := lowering_word_weight_or_nMinus hs hv.2.1 hu'
      change Θ mu (u' v) ∈ highestWeightSpace E mu ⊔ (nMinus E ⊓ weightSp E mu)
      rw [hΘ mu κ _ hκ]
      split_ifs with hk
      · subst hk
        rcases h with h | h
        · refine Submodule.mem_sup_left (mem_highestWeightSpace_iff.2 ⟨hκ, ?_⟩)
          rw [h]
          exact hv.2.2
        · exact Submodule.mem_sup_right ⟨h, hκ⟩
      · exact Submodule.zero_mem _
    exact hY (lowering_word_span_enveloping_stable hE hv hu v (Submodule.subset_span ⟨1, Submonoid.one_mem _, rfl⟩))
  intro x hx
  have h1 : x ∈ (highestWeightSpace E mu ⊔ (nMinus E ⊓ weightSp E mu)).comap (Θ mu) := by
    have : (⊤ : Submodule K V) ≤ (highestWeightSpace E mu ⊔ (nMinus E ⊓ weightSp E mu)).comap (Θ mu) := by
      rw [← htop]
      exact iSup_le hle
    exact this Submodule.mem_top
  have h2 : Θ mu x ∈ highestWeightSpace E mu ⊔ (nMinus E ⊓ weightSp E mu) := h1
  rwa [hΘ mu mu x hx, if_pos rfl] at h2

theorem extremal_projector_of_reducibility (D : Formalism.BasicNotions.D7) (h : adm5 D) : SimpleRaisingKillsExtremalProjector := by
  intro K V _ _ _ _ _ n E hE mu hmu ord hord T hT x hx a b hab
  obtain ⟨_, h2, h3⟩ := h K V n E hE mu hmu ord hord T hT
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (weightSpace_le_hwv_sup_nMinus D E hE mu hx)
  obtain ⟨hy1, hy2⟩ := mem_highestWeightSpace_iff.1 hy
  rw [map_add, h3 y hy1 hy2, h2 z hz.2 hz.1, add_zero]
  exact hy2 a b (by
    have : (a : ℕ) < (b : ℕ) := by omega
    exact this)

theorem condition_iff_additive_maps (D : Formalism.BasicNotions.D7) : adm5 D ↔ SimpleRaisingKillsExtremalProjector := ⟨extremal_projector_of_reducibility D, sizes_bound_of_log_estimates D⟩

end Formalism.MainNotions.G.GLWeightTheory
