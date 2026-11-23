import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalEndomorphisms.IsUniformInducingOfVal

open NumberField IsDedekindDomain Polynomial

namespace PI.LocalEndW

private theorem aeval_ringHom_apply_lemma {L M : Type*} [Field L] [Field M] [Algebra ℚ L] [Algebra ℚ M]
    (φ : L →+* M) (p : ℚ[X]) (x : L) : aeval (φ x) p = φ (aeval x p) := by
  rw [aeval_def, aeval_def, hom_eval₂, RingHom.ext_rat (φ.comp (algebraMap ℚ L)) (algebraMap ℚ M)]

theorem algebraMap_mem_range {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}
    (τ : v.adicCompletion F →+* v.adicCompletion F) (a : F) :
    algebraMap F (v.adicCompletion F) a ∈ Set.range τ := by
  set K := v.adicCompletion F
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  let _ : Algebra ℚ K := DivisionRing.toRatAlgebra
  set p := minpoly ℚ a with hp
  have hp0 : p ≠ 0 := minpoly.ne_zero (IsIntegral.of_finite ℚ a)
  set S : Set K := p.rootSet K
  have hmem : ∀ x : K, x ∈ S ↔ aeval x p = 0 := fun x => by
    rw [mem_rootSet]
    exact ⟨fun h => h.2, fun h => ⟨hp0, h⟩⟩
  have haS : algebraMap F K a ∈ S := by
    rw [hmem, aeval_ringHom_apply_lemma (algebraMap F K) p a, hp, minpoly.aeval, map_zero]
  have hmaps : Set.MapsTo τ S S := fun x hx => by
    rw [hmem] at hx ⊢
    rw [aeval_ringHom_apply_lemma τ p x, hx, map_zero]
  have : Finite S := (rootSet_finite p K).to_subtype
  let g : S → S := hmaps.restrict τ S S
  have hg : Function.Injective g := fun x y h => Subtype.ext (τ.injective (congrArg Subtype.val h))
  obtain ⟨r, hr⟩ := Finite.surjective_of_injective hg ⟨algebraMap F K a, haS⟩
  exact ⟨r.1, congrArg Subtype.val hr⟩

private theorem denseRange_algebraMap_adicCompletion_lemma_2 {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) : DenseRange (algebraMap F (v.adicCompletion F)) := by
  exact HeightOneSpectrum.denseRange_algebraMap F v

theorem valSurjective : ValSurjective := by
  intro F _ _ v τ hτ y
  have hclosed : IsClosed (Set.range τ) :=
    (isUniformInducing_of_val τ hτ).isComplete_range.isClosed
  have hdense : Dense (Set.range τ) :=
    (denseRange_algebraMap_adicCompletion_lemma_2 v).mono (by
      rintro _ ⟨a, rfl⟩
      exact algebraMap_mem_range τ a)
  have huniv := hdense.closure_eq
  rw [hclosed.closure_eq] at huniv
  have hy : y ∈ Set.range τ := huniv ▸ Set.mem_univ y
  exact hy

end PI.LocalEndW
