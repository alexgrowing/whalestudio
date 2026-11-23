import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdmissibleIntegralBasisChangeOne

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

namespace GlobalTheory.Nef

open IntermediateField

theorem finiteDimensional_adjoin_of_trdeg_le_one {k F : Type} [Field k] [Field F] [Algebra k F]
    [Algebra.EssFiniteType k F] (htr : Algebra.trdeg k F ≤ 1) (x : F) (hx : Transcendental k x) :
    FiniteDimensional k⟮x⟯ F := by
  have hind : AlgebraicIndependent k (fun _ : Unit => x) :=
    algebraicIndependent_unique_type_iff.mpr hx
  have hb : IsTranscendenceBasis k (fun _ : Unit => x) :=
    hind.isTranscendenceBasis_of_trdeg_le_of_finite (by simpa using htr)
  have halg : Algebra.IsAlgebraic k⟮x⟯ F := by
    have := hb.isAlgebraic_field
    rwa [Set.range_const] at this
  have : Algebra.EssFiniteType k⟮x⟯ F := Algebra.EssFiniteType.of_comp k k⟮x⟯ F
  obtain ⟨S, hS⟩ := IntermediateField.fg_top_iff.mpr this
  have hfin : FiniteDimensional k⟮x⟯ (adjoin k⟮x⟯ (S : Set F)) :=
    IntermediateField.finiteDimensional_adjoin fun y _ => (Algebra.IsAlgebraic.isAlgebraic y).isIntegral
  rw [hS] at hfin
  exact LinearEquiv.finiteDimensional (IntermediateField.topEquiv (F := k⟮x⟯) (E := F)).toLinearEquiv

theorem essFiniteType_trdeg_of_isFF {k F : Type} [Field k] [Field F] [Algebra k F] (h : IsFF k F) :
    Algebra.EssFiniteType k F ∧ Algebra.trdeg k F ≤ 1 := by
  obtain ⟨t, ht, hfin⟩ := h
  have h1 : Algebra.EssFiniteType k k⟮t⟯ :=
    IntermediateField.essFiniteType_iff.mpr ⟨{t}, by simp⟩
  refine ⟨Algebra.EssFiniteType.comp k k⟮t⟯ F, ?_⟩
  open IntermediateField.algebraAdjoinAdjoin in
  have : Algebra.IsAlgebraic (Algebra.adjoin k {t}) F := Algebra.IsAlgebraic.trans _ k⟮t⟯ _
  have hind : AlgebraicIndependent k (fun _ : Unit => t) :=
    algebraicIndependent_unique_type_iff.mpr ht
  have hb : IsTranscendenceBasis k (fun _ : Unit => t) :=
    hind.isTranscendenceBasis_iff_isAlgebraic.mpr (by rwa [Set.range_const])
  rw [← hb.cardinalMk_eq_trdeg]
  simp

theorem isFF_main : ∀ (k F : Type) [Field k] [Field F] [Algebra k F], IsFF k F →
    (∀ x : F, Transcendental k x → FiniteDimensional k⟮x⟯ F) ∧
    ∀ (E : Type) [Field E] [Algebra k E] [Algebra F E] [IsScalarTower k F E] [FiniteDimensional F E], IsFF k E := by
  intro k F _ _ _ h
  obtain ⟨hfg, htr⟩ := essFiniteType_trdeg_of_isFF h
  refine ⟨fun x hx => finiteDimensional_adjoin_of_trdeg_le_one htr x hx, ?_⟩
  intro E _ _ _ _ _
  have hfgE : Algebra.EssFiniteType k E := Algebra.EssFiniteType.comp k F E
  have h0 : Algebra.trdeg F E = 0 := trdeg_eq_zero_iff.mpr inferInstance
  have htrE : Algebra.trdeg k E ≤ 1 := by
    rw [← trdeg_add_eq k F, h0, add_zero]; exact htr
  obtain ⟨t, ht, _⟩ := h
  have ht' : Transcendental k (algebraMap F E t) :=
    (transcendental_algebraMap_iff (algebraMap F E).injective).mpr ht
  exact ⟨algebraMap F E t, ht', finiteDimensional_adjoin_of_trdeg_le_one htrE _ ht'⟩

end GlobalTheory.Nef
