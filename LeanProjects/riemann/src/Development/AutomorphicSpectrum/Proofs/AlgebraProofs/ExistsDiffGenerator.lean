import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT

open Module NumberField

theorem diffGen_v_le_one {C : Type} [Field C] (v : Valuation C NNReal)
    {E : Type} [Field E] [NumberField E] (σ : E →+* C) (a : 𝓞 E) : v (σ (a : E)) ≤ 1 := by
  have h1 : IsIntegral ℤ (σ (a : E)) := (RingOfIntegers.isIntegral_coe a).map σ.toIntAlgHom
  have h2 : IsIntegral v.integer (σ (a : E)) := h1.tower_top
  exact (Valuation.integer.integers v).mem_of_integral h2

theorem diffGen_exists_max {C : Type} [Field C] (v : Valuation C NNReal)
    {E : Type} [Field E] [NumberField E] (σ : E →+* C) (D : Ideal (𝓞 E)) :
    ∃ x₀ ∈ D, ∀ x ∈ D, v (σ ((x : 𝓞 E) : E)) ≤ v (σ ((x₀ : 𝓞 E) : E)) := by
  classical
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian D : D.FG)
  rcases s.eq_empty_or_nonempty with h | h
  · refine ⟨0, D.zero_mem, fun x hx => ?_⟩
    rw [← hs, h, Finset.coe_empty, Submodule.span_empty, Submodule.mem_bot] at hx
    simp [hx]
  · obtain ⟨x₀, hx₀s, hmax⟩ := s.exists_max_image (fun g : 𝓞 E => v (σ (g : E))) h
    refine ⟨x₀, ?_, fun x hx => ?_⟩
    · rw [← hs]
      exact Submodule.subset_span hx₀s
    rw [← hs] at hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact hmax y hy
    | zero => simp
    | add y z _ _ hy hz =>
      calc v (σ ((y + z : 𝓞 E) : E)) = v (σ (y : E) + σ (z : E)) := by simp
        _ ≤ max (v (σ (y : E))) (v (σ (z : E))) := v.map_add _ _
        _ ≤ _ := max_le hy hz
    | smul r y _ hy =>
      calc v (σ ((r • y : 𝓞 E) : E)) = v (σ (r : E)) * v (σ (y : E)) := by simp [smul_eq_mul]
        _ ≤ 1 * v (σ (x₀ : E)) := mul_le_mul' (diffGen_v_le_one v σ r) hy
        _ = _ := one_mul _

theorem exists_diff_generator (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O]
    [Algebra O C] (hv : v.Integers O) [CharZero C] (E : Type) [Field E] [NumberField E]
    (σ : E →+* C) :
    (∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap O C).range) ∧
      ∃ d : O, algebraMap O C d ≠ 0 ∧ v (algebraMap O C d) = diffAbs v σ ∧
        Submodule.span O {algebraMap O C d} =
          Submodule.span O {y : C | ∃ x ∈ differentIdeal ℤ (𝓞 E), y = σ (x : E)} := by
  have hint : ∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap O C).range := by
    intro a
    have h1 : IsIntegral ℤ (σ (a : E)) := (a.isIntegral_coe).map σ.toIntAlgHom
    have h3 : σ (a : E) ∈ v.integer := hv.mem_of_integral (h1.tower_top (A := O))
    exact RingHom.mem_range.2 (hv.exists_of_le_one ((Valuation.mem_integer_iff v _).1 h3))
  refine ⟨hint, ?_⟩
  obtain ⟨x₀, hx₀, hmax⟩ := diffGen_exists_max v σ (differentIdeal ℤ (𝓞 E))
  obtain ⟨d, hd⟩ := RingHom.mem_range.1 (hint x₀)
  have hne : differentIdeal ℤ (𝓞 E) ≠ ⊥ := differentIdeal_ne_bot
  obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hσz : σ (z : E) ≠ 0 := (map_ne_zero σ).2 (by simpa using hz0)
  have hx0ne : σ (x₀ : E) ≠ 0 := by
    intro h
    have hle := hmax z hz
    rw [h, map_zero] at hle
    exact (v.ne_zero_iff.2 hσz) (le_antisymm hle zero_le)
  refine ⟨d, by rw [hd]; exact hx0ne, ?_, ?_⟩
  · rw [hd, diffAbs]
    apply le_antisymm
    · exact le_ciSup (f := fun x : differentIdeal ℤ (𝓞 E) => v (σ ((x : 𝓞 E) : E)))
        ⟨v (σ (x₀ : E)), by rintro _ ⟨x, rfl⟩; exact hmax x x.2⟩ ⟨x₀, hx₀⟩
    · exact ciSup_le fun x => hmax x x.2
  · rw [hd]
    apply le_antisymm
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact Submodule.subset_span ⟨x₀, hx₀, rfl⟩
    · rw [Submodule.span_le]
      rintro y ⟨x, hx, rfl⟩
      have hle : v (σ (x : E) / σ (x₀ : E)) ≤ 1 := by
        rw [map_div₀]
        exact div_le_one_of_le₀ (hmax x hx) zero_le
      obtain ⟨c, hc⟩ := hv.exists_of_le_one hle
      rw [SetLike.mem_coe, Submodule.mem_span_singleton]
      refine ⟨c, ?_⟩
      rw [Algebra.smul_def, hc, div_mul_cancel₀ _ hx0ne]

end GlobalTheory.CompanionTheory.Ar.HT
