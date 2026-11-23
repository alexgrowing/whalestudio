import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.ThickPre

lemma thickTrans_surj (R' : Type) [CommRing R'] (I : Ideal R') (e : ℕ)
    (t : Spec (CommRingCat.of (R' ⧸ I ^ (e + 1 + 1)))) : ∃ t', (thickTrans R' I e) t' = t := by
  have hs : Function.Surjective (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1))) :
      R' ⧸ I ^ (e + 1 + 1) →+* R' ⧸ I ^ (e + 1)) := Ideal.Quotient.factor_surjective _
  have hr := _root_.range_comap_of_surjective _ _ hs
  have ht : (t : PrimeSpectrum _) ∈ Set.range (PrimeSpectrum.comap
      (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1))) :
        R' ⧸ I ^ (e + 1 + 1) →+* R' ⧸ I ^ (e + 1))) := by
    rw [hr]
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    have ha : a ∈ I ^ (e + 1) := by
      rw [SetLike.mem_coe, RingHom.mem_ker, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] at hx
      exact hx
    have h2 : (Ideal.Quotient.mk (I ^ (e + 1 + 1)) a) ^ 2 = 0 := by
      rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
      have : a ^ 2 ∈ I ^ ((e + 1) * 2) := by rw [pow_mul]; exact Ideal.pow_mem_pow ha 2
      exact Ideal.pow_le_pow_right (by omega) this
    exact t.isPrime.mem_of_pow_mem 2 (by rw [h2]; exact Ideal.zero_mem _)
  obtain ⟨t', ht'⟩ := ht
  exact ⟨t', ht'⟩

lemma thickMap_surj (R' : Type) [CommRing R'] (I : Ideal R') (e : ℕ) (G' : Over (Sp R')) :
    Function.Surjective (thickMap R' I e G') := by
  intro y
  obtain ⟨t', ht'⟩ := thickTrans_surj R' I e (pullback.snd G'.hom (thick R' I (e + 1)) y)
  have hc : G'.hom (pullback.fst G'.hom (thick R' I (e + 1)) y) = thick R' I e t' := by
    have h1 : G'.hom (pullback.fst G'.hom (thick R' I (e + 1)) y) =
        thick R' I (e + 1) (pullback.snd G'.hom (thick R' I (e + 1)) y) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
    rw [h1, ← ht', ← Scheme.Hom.comp_apply, thickTrans_comp]
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback _ _ hc
  refine ⟨z, (pullback.fst G'.hom (thick R' I (e + 1))).isClosedEmbedding.injective ?_⟩
  rw [← Scheme.Hom.comp_apply, thickMap, pullback.lift_fst, Category.comp_id, hz]

end GlobalTheory.Mum.ThickPre

theorem GlobalTheory.Mum.thick_preimage_eq (R' : Type) [CommRing R'] (I : Ideal R') (G' : Over (Sp R')) (Y : Scheme.{0})
    (φ : ∀ e : ℕ, (thickObj R' I e G').left ⟶ Y) (hφ : ∀ e, thickMap R' I e G' ≫ φ (e + 1) = φ e)
    (V : G'.left.Opens) (W : Y.Opens)
    (h0 : φ 0 ⁻¹ᵁ W = (pullback.fst G'.hom (thick R' I 0)) ⁻¹ᵁ V) :
    ∀ e, φ e ⁻¹ᵁ W = (pullback.fst G'.hom (thick R' I e)) ⁻¹ᵁ V := by
  intro e
  induction e with
  | zero => exact h0
  | succ e ih =>
    have h1 : thickMap R' I e G' ⁻¹ᵁ (φ (e + 1) ⁻¹ᵁ W) =
        thickMap R' I e G' ⁻¹ᵁ ((pullback.fst G'.hom (thick R' I (e + 1))) ⁻¹ᵁ V) := by
      rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hφ, ih, thickMap, pullback.lift_fst,
        Category.comp_id]
    ext y
    obtain ⟨x, rfl⟩ := GlobalTheory.Mum.ThickPre.thickMap_surj R' I e G' y
    have := congrArg (fun U : Scheme.Opens _ => x ∈ U) h1
    simpa using this

example : ∀ (R' : Type) [CommRing R'] (I : Ideal R') (G' : Over (Sp R')) (Y : Scheme.{0}) (φ : ∀ e : ℕ, (thickObj R' I e G').left ⟶ Y), (∀ e, thickMap R' I e G' ≫ φ (e + 1) = φ e) → ∀ (V : G'.left.Opens) (W : Y.Opens), φ 0 ⁻¹ᵁ W = (pullback.fst G'.hom (thick R' I 0)) ⁻¹ᵁ V → ∀ e, φ e ⁻¹ᵁ W = (pullback.fst G'.hom (thick R' I e)) ⁻¹ᵁ V :=
  @GlobalTheory.Mum.thick_preimage_eq
