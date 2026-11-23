import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.QuadraticSplitting.QuadSplit

noncomputable section

open UpperTheory.V.Sd.S2 ReciprocityTheory.Gal

namespace UpperTheory

private theorem mix_cont {k X : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] [TopologicalSpace X] (γ : kˣ)
    {A B : X → Matrix (Fin 2) (Fin 2) k} (hA : Continuous A) (hB : Continuous B) :
    Continuous fun x => mix γ (A x) (B x) := by
  have a : ∀ i j, Continuous fun x => A x i j := fun i j => hA.matrix_elem i j
  have b : ∀ i j, Continuous fun x => B x i j := fun i j => hB.matrix_elem i j
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [mix, div_eq_mul_inv] <;> fun_prop

theorem continuous_mix_family : UpperTheory.V.Sd.S2.MixCont := by
  intro l _ Γ₀ Γ _ _ _ _ _ j t α β ρ R hM hj hρ
  haveI hN : j.range.Normal := Subgroup.normal_of_index_eq_two hM.index
  have hc : ∀ h : Γ₀, ∃ h', j h' = t⁻¹ * j h * t := fun h => by
    have := hN.conj_mem (j h) ⟨h, rfl⟩ t⁻¹
    simpa using this
  choose c hc using hc
  have cc : Continuous c := by
    rw [hj.isInducing.continuous_iff]
    have : (j ∘ c) = fun h => t⁻¹ * j h * t := funext hc
    rw [this]
    have := hj.continuous
    fun_prop
  have ci : Continuous fun h : Γ₀ => h⁻¹ := by
    rw [hj.isInducing.continuous_iff]
    have : (j ∘ fun h : Γ₀ => h⁻¹) = fun h => (j h)⁻¹ := funext fun h => by simp
    rw [this]
    exact hj.continuous.inv
  have hv : Continuous fun h => (ρ h).val := Units.continuous_val.comp hρ
  have h1 : Continuous fun h => (R (j h)).val := by
    have : (fun h => (R (j h)).val) = fun h => mix (β / α) (ρ h) (ρ (c h)) :=
      funext fun h => hM.on h (c h) (hc h)
    rw [this]
    exact mix_cont _ hv (hv.comp cc)
  have h2 : Continuous (R ∘ j) := by
    rw [Units.continuous_iff]
    refine ⟨h1, ?_⟩
    have := h1.comp ci
    refine this.congr fun h => ?_
    simp only [Function.comp, map_inv]
  refine continuous_of_continuousAt_one R ?_
  have := (hj.continuousAt_iff (g := R) (x := 1)).1 h2.continuousAt
  rwa [map_one] at this

end UpperTheory
