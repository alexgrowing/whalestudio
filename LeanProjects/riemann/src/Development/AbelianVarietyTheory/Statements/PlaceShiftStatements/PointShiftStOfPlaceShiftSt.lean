import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.PlaceShiftSt

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatCM.PlaceShiftModel

open NumberField IsDedekindDomain GlobalTheory.CompHt GlobalTheory.HTLat

theorem det_ne_zero {O C U : Type} [CommRing O] [Field C] [Algebra O C] [AddCommGroup U] [Module C U] [Module O U]
    [IsScalarTower O C U] {n : ℕ} {La : Submodule O U} {b : Fin n → U} {g : Matrix (Fin n) (Fin n) C}
    (h : IsLatBasis C La fun i => ∑ j, g i j • b j) : g.det ≠ 0 := by
  have hl : LinearIndependent C g.row :=
    LinearIndependent.of_comp (Fintype.linearCombination C b) h.1
  exact ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_rows_iff_isUnit.1 hl)).ne_zero

variable {E : Type} [Field E] [NumberField E] {ℓ : ℕ} [Fact ℓ.Prime]

theorem norm_le_one (τ : E →+* ℂ_[ℓ]) (a : 𝓞 E) : ‖τ (a : E)‖ ≤ 1 := by
  rw [← algebraMap_embO (PadicComplexInt.integers ℓ) τ a]
  exact (GlobalTheory.PadicComplexHost.mem_iff_norm _ _).1 (Subtype.prop _)

theorem norm_ell : ‖(ℓ : ℂ_[ℓ])‖ < 1 := by
  rw [← map_natCast (algebraMap ℚ_[ℓ] ℂ_[ℓ]), norm_algebraMap']
  exact Padic.norm_p_lt_one

theorem exists_place (τ : E →+* ℂ_[ℓ]) :
    ∃ w : HeightOneSpectrum (𝓞 E), ∀ a : 𝓞 E, a ∈ w.asIdeal ↔ ‖τ (a : E)‖ < 1 := by
  let I : Ideal (𝓞 E) :=
    { carrier := {a | ‖τ (a : E)‖ < 1}
      add_mem' := fun {a b} ha hb => by
        change ‖τ ((a + b : 𝓞 E) : E)‖ < 1
        rw [RingOfIntegers.coe_eq_algebraMap, map_add, map_add]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ha hb)
      zero_mem' := by simp
      smul_mem' := fun c a ha => by
        change ‖τ ((c * a : 𝓞 E) : E)‖ < 1
        rw [RingOfIntegers.coe_eq_algebraMap, map_mul, map_mul, norm_mul]
        exact mul_lt_one_of_nonneg_of_lt_one_right (norm_le_one τ c) (norm_nonneg _) ha }
  refine ⟨⟨I, ⟨fun h => ?_, fun {a b} h => ?_⟩, fun h => ?_⟩, fun _ => Iff.rfl⟩
  · have : ‖τ ((1 : 𝓞 E) : E)‖ < 1 := (Ideal.eq_top_iff_one I).1 h
    simp at this
  · by_contra hn
    rw [not_or] at hn
    have ha : ‖τ (a : E)‖ = 1 := le_antisymm (norm_le_one τ a) (not_lt.1 hn.1)
    have hb : ‖τ (b : E)‖ = 1 := le_antisymm (norm_le_one τ b) (not_lt.1 hn.2)
    have h' : ‖τ ((a * b : 𝓞 E) : E)‖ < 1 := h
    rw [RingOfIntegers.coe_eq_algebraMap, map_mul, map_mul, norm_mul] at h'
    rw [RingOfIntegers.coe_eq_algebraMap] at ha hb
    rw [ha, hb] at h'
    simp at h'
  · have : (ℓ : 𝓞 E) ∈ I := by
      change ‖τ ((ℓ : 𝓞 E) : E)‖ < 1
      rw [RingOfIntegers.coe_eq_algebraMap, map_natCast, map_natCast]
      exact norm_ell
    rw [h, Ideal.mem_bot] at this
    exact (Fact.out : ℓ.Prime).ne_zero (by exact_mod_cast this)

theorem exists_place_emb (E : Type) [Field E] [NumberField E] (ℓ : ℕ) [Fact ℓ.Prime] :
    ∃ (w : HeightOneSpectrum (𝓞 E)) (τ : E →+* ℂ_[ℓ]), ∀ a : 𝓞 E, a ∈ w.asIdeal ↔ ‖τ (a : E)‖ < 1 := by
  have : Nonempty (E →+* ℂ_[ℓ]) := Fintype.card_pos_iff.1 (by
    rw [NumberField.Embeddings.card]; exact Module.finrank_pos)
  obtain ⟨τ⟩ := this
  obtain ⟨w, hw⟩ := exists_place τ
  exact ⟨w, τ, hw⟩

theorem pointShiftSt_of_placeShiftSt (h : PlaceShiftSt) : PointShiftSt := by
  intro E _ _ _ H hH ℓ _ τ
  obtain ⟨w, hw⟩ := exists_place τ
  obtain ⟨κ₁, κ₂, hκ⟩ := h E H hH ℓ w
  exact ⟨κ₁, κ₂, hκ τ hw⟩

end GlobalTheory.FlatCM.PlaceShiftModel

end
