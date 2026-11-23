import Mathlib
import ReciprocityTheory.ReductiveGroups.ExtensionEmbeddings.ExtEmb

open NumberField IsDedekindDomain
open scoped Cardinal Polynomial IntermediateField

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem mk_le_aleph0_of_finite (F : IntermediateField ℚ ℂ) (hF : FiniteDimensional ℚ F) :
    Cardinal.mk F ≤ Cardinal.aleph0 := by
  have h := Algebra.IsAlgebraic.cardinalMk_le_max ℚ F
  simpa using h

theorem mk_ratFunc_le_aleph0 (F : Type) [Field F] (hF : Cardinal.mk F ≤ Cardinal.aleph0) :
    Cardinal.mk (RatFunc F) ≤ Cardinal.aleph0 := by
  have : Countable F[X] :=
    Cardinal.mk_le_aleph0_iff.1 (Polynomial.cardinalMk_le_max.trans (max_le hF le_rfl))
  have hs : Function.Surjective (fun p : F[X] × F[X] =>
      algebraMap F[X] (RatFunc F) p.1 / algebraMap F[X] (RatFunc F) p.2) := by
    intro x
    obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := F[X]) x
    exact ⟨(a, b), rfl⟩
  have : Countable (RatFunc F) := hs.countable
  exact Cardinal.mk_le_aleph0

theorem exists_moved_of_transcendental (F : IntermediateField ℚ ℂ)
    (hF : Cardinal.mk F ≤ Cardinal.aleph0) (c : ℂ) (hc : Transcendental F c) :
    ∃ g : ℂ ≃+* ℂ, (∀ a ∈ F, g a = a) ∧ g c ≠ c := by
  have hc1 : Transcendental F (c + 1) := fun h =>
    hc (by simpa using h.sub (isAlgebraic_one (R := F) (A := ℂ)))
  have i0 : Function.Injective (Polynomial.aeval (R := F) c).toRingHom :=
    transcendental_iff_injective.1 hc
  have i1 : Function.Injective (Polynomial.aeval (R := F) (c + 1)).toRingHom :=
    transcendental_iff_injective.1 hc1
  let f : RatFunc F →+* ℂ := IsFractionRing.lift i0
  let g : RatFunc F →+* ℂ := IsFractionRing.lift i1
  obtain ⟨σ, hσ⟩ := ReciprocityTheory.ChartRestriction.B3.iop_extEmb f g (mk_ratFunc_le_aleph0 F hF)
    (by simp [Cardinal.mk_complex, Cardinal.aleph0_lt_continuum]) rfl
  have hfa : ∀ p : F[X], f (algebraMap F[X] (RatFunc F) p) = Polynomial.aeval c p := fun p =>
    IsFractionRing.lift_algebraMap i0 p
  have hga : ∀ p : F[X], g (algebraMap F[X] (RatFunc F) p) = Polynomial.aeval (c + 1) p := fun p =>
    IsFractionRing.lift_algebraMap i1 p
  refine ⟨σ, fun a ha => ?_, fun h => ?_⟩
  · have := hσ (algebraMap F[X] (RatFunc F) (Polynomial.C ⟨a, ha⟩))
    rw [hfa, hga] at this
    simpa using this
  · have := hσ (algebraMap F[X] (RatFunc F) Polynomial.X)
    rw [hfa, hga] at this
    simp only [Polynomial.aeval_X] at this
    rw [h] at this
    simpa using this

theorem exists_moved_of_isAlgebraic (F : IntermediateField ℚ ℂ)
    (hF : Cardinal.mk F ≤ Cardinal.aleph0) (c : ℂ) (hc : IsAlgebraic F c) (hcF : c ∉ F) :
    ∃ g : ℂ ≃+* ℂ, (∀ a ∈ F, g a = a) ∧ g c ≠ c := by
  have hi : IsIntegral F c := hc.isIntegral
  have hsep : (minpoly F c).Separable := (minpoly.irreducible hi).separable
  have hsplit : ((minpoly F c).map (algebraMap F ℂ)).Splits := IsAlgClosed.splits _
  have hdeg : (minpoly F c).natDegree ≠ 1 := by
    intro h1
    have : (minpoly F c).degree = 1 := by
      rw [Polynomial.degree_eq_natDegree (minpoly.ne_zero hi), h1]; rfl
    obtain ⟨a, rfl⟩ := minpoly.mem_range_of_degree_eq_one F c this
    exact hcF a.2
  have hpos := minpoly.natDegree_pos hi
  have hcard := Polynomial.card_rootSet_eq_natDegree (K := ℂ) hsep hsplit
  have hmem : c ∈ (minpoly F c).rootSet ℂ := by
    rw [Polynomial.mem_rootSet]
    exact ⟨minpoly.ne_zero hi, minpoly.aeval F c⟩
  obtain ⟨⟨c', hc'⟩, hne⟩ := Fintype.exists_ne_of_one_lt_card
    (by rw [hcard]; omega) (⟨c, hmem⟩ : (minpoly F c).rootSet ℂ)
  have hne' : c' ≠ c := fun h => hne (Subtype.ext h)
  have hroot : c' ∈ (minpoly F c).aroots ℂ := by
    rw [Polynomial.mem_aroots]
    exact (Polynomial.mem_rootSet.1 hc')
  let g0 : F⟮c⟯ →ₐ[F] ℂ := (IntermediateField.algHomAdjoinIntegralEquiv F hi).symm ⟨c', hroot⟩
  have hg0 : g0 (IntermediateField.AdjoinSimple.gen F c) = c' :=
    IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen F hi ⟨c', hroot⟩
  have hfin : FiniteDimensional F F⟮c⟯ := IntermediateField.adjoin.finiteDimensional hi
  have hE : Cardinal.mk F⟮c⟯ ≤ Cardinal.aleph0 :=
    (Algebra.IsAlgebraic.cardinalMk_le_max F F⟮c⟯).trans (max_le hF le_rfl)
  obtain ⟨σ, hσ⟩ := ReciprocityTheory.ChartRestriction.B3.iop_extEmb (algebraMap F⟮c⟯ ℂ) g0.toRingHom hE
    (by simp [Cardinal.mk_complex, Cardinal.aleph0_lt_continuum]) rfl
  refine ⟨σ, fun a ha => ?_, fun h => ?_⟩
  · have := hσ (algebraMap F F⟮c⟯ ⟨a, ha⟩)
    have h2 : g0.toRingHom (algebraMap F F⟮c⟯ ⟨a, ha⟩) = a := by
      simpa using g0.commutes ⟨a, ha⟩
    rw [h2] at this
    simpa using this
  · have := hσ (IntermediateField.AdjoinSimple.gen F c)
    have h2 : algebraMap F⟮c⟯ ℂ (IntermediateField.AdjoinSimple.gen F c) = c := rfl
    rw [h2, h] at this
    exact hne' (hg0.symm.trans this.symm)

theorem mem_of_fixed_aut : ∀ (F : IntermediateField ℚ ℂ) (c : ℂ), FiniteDimensional ℚ F →
    (∀ g : ℂ ≃+* ℂ, (∀ a ∈ F, g a = a) → g c = c) → c ∈ F := by
  intro F c hF h
  by_contra hcF
  have hcount := mk_le_aleph0_of_finite F hF
  by_cases hc : IsAlgebraic F c
  · obtain ⟨g, hg, hne⟩ := exists_moved_of_isAlgebraic F hcount c hc hcF
    exact hne (h g hg)
  · obtain ⟨g, hg, hne⟩ := exists_moved_of_transcendental F hcount c hc
    exact hne (h g hg)

end GlobalTheory.CompanionTheory.Ar.Flat
