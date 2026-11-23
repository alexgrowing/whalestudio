import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLatIntVec
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.NormSig

theorem norm_eq_mul_conj_and_absNorm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ t : 𝓞 E, algebraMap F E ((RingOfIntegers.norm F t : 𝓞 F) : F) = (t : E) * σ (t : E) ∧ Ideal.absNorm (Ideal.span {RingOfIntegers.norm F t}) = Ideal.absNorm (Ideal.span {t}) := by
  intro F E _ _ _ _ _ σ hσ t
  classical
  obtain ⟨_, hE, hdeg, hconj⟩ := hσ
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hdeg]; norm_num)
  refine ⟨?_, ?_⟩
  · set σ' : E ≃ₐ[F] E := AlgEquiv.ofBijective σ (AlgHom.bijective σ) with hσ'
    have hne : σ' ≠ 1 := by
      intro h
      have hx : ∀ x, σ x = x := fun x => by
        have := congrArg (fun g : E ≃ₐ[F] E => g x) h
        simpa [hσ'] using this
      obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace E))
      have hwc : w.IsComplex := hE.isComplex w
      rw [InfinitePlace.isComplex_iff] at hwc
      apply hwc
      rw [ComplexEmbedding.isReal_iff]
      ext x
      rw [ComplexEmbedding.conjugate_coe_eq, starRingEnd_apply, ← hconj, hx]
    have hcard_le : Fintype.card (E ≃ₐ[F] E) ≤ 2 := by
      rw [← hdeg]
      exact (Fintype.card_le_of_injective (fun g : E ≃ₐ[F] E => (g : E →ₐ[F] E))
        (fun a b h => AlgEquiv.ext fun x => DFunLike.congr_fun h x)).trans AlgHom.card_le
    have huniv : (Finset.univ : Finset (E ≃ₐ[F] E)) = {1, σ'} := by
      symm
      apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
      rw [Finset.card_univ, Finset.card_pair hne.symm]
      exact hcard_le
    haveI : IsGalois F E := IsGalois.of_card_aut_eq_finrank F E (by
      rw [hdeg, Nat.card_eq_fintype_card]
      apply le_antisymm hcard_le
      rw [← Finset.card_univ, huniv, Finset.card_pair hne.symm])
    rw [RingOfIntegers.coe_norm, Algebra.norm_eq_prod_automorphisms, huniv, Finset.prod_pair hne.symm]
    simp [hσ']
  · rw [Ideal.absNorm_span_singleton, Ideal.absNorm_span_singleton]
    congr 1
    apply Int.cast_injective (α := ℚ)
    rw [Algebra.coe_norm_int, Algebra.coe_norm_int, RingOfIntegers.coe_norm, Algebra.norm_norm]

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.NormSig
