import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.QuadraticSplitting.QuadSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Base UpperTheory.V.Ws UpperTheory.V.Sd.S2

private theorem exists_sign_character_index_two {Γ R : Type} [Group Γ] [CommRing R] (H : Subgroup Γ) (h : H.index = 2) :
    ∃ φ : Γ →* Rˣ, (∀ g ∈ H, φ g = 1) ∧ ∀ g ∉ H, φ g = -1 := by
  classical
  refine ⟨MonoidHom.mk' (fun g => if g ∈ H then 1 else -1) fun a b => ?_, fun g hg => if_pos hg, fun g hg => if_neg hg⟩
  by_cases ha : a ∈ H <;> by_cases hb : b ∈ H <;> simp [Subgroup.mul_mem_iff_of_index_two h, ha, hb]

theorem UpperTheory.exists_quadratic_character_of_subgroup_index_two :
    UpperTheory.V.Sd.S2.HypEx := by
  intro Ω _ _ _ l _ c D T hg hok htwo hdeep
  obtain ⟨k₀, hdeg, hreal, hsp, hps⟩ := htwo.quad
  haveI : FiniteDimensional ℚ k₀ := Module.finite_of_finrank_pos (by omega)
  haveI hnf : NumberField k₀ := {}
  haveI : IsAlgClosure k₀ Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) k₀⟩
  obtain ⟨hE, hO, hI⟩ := galEmbTop ℚ k₀ Ω
  have hfix : galOf ℚ k₀ Ω = k₀.fixingSubgroup := by
    ext σ
    rw [mem_galOf, IntermediateField.mem_fixingSubgroup_iff]
    exact ⟨fun h x hx => h ⟨x, hx⟩, fun h x => h x.1 x.2⟩
  have hr : (resQ k₀).range = k₀.fixingSubgroup := (range_galEmb ℚ k₀ Ω).trans hfix
  have hidx : k₀.fixingSubgroup.index = 2 := by rw [← hfix, hI, hdeg]
  obtain ⟨φ, h1, h2⟩ := exists_sign_character_index_two (R := PadicAlgCl l) k₀.fixingSubgroup hidx
  refine ⟨k₀, hnf, hreal, φ, ⟨hg, hok, htwo, hdeep, hdeg, ?_, ?_, hps, h1, h2⟩, hr, hidx, hE, ?_⟩
  · exact hsp 2 (by simp)
  · exact hsp l (by simp)
  · rw [← MonoidHom.coe_range, hr, ← hfix]
    exact hO
