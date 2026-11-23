import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImV
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FormallyUnramifiedRingOfIntegersIffDifferentIdea
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HaarMeasureGramGL2ActionTensor
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical

namespace GlobalTheory

open NumberField IsDedekindDomain MeasureTheory Matrix in
open scoped TensorProduct ENNReal nonZeroDivisors Classical in
private theorem algebraMap_trace_eq_add_of_ne_id {F E : Type} [Field F] [Field E] [Algebra F E]
    [Algebra.IsSeparable F E] (h2 : Module.finrank F E = 2) (σ : E →ₐ[F] E)
    (hσ : σ ≠ AlgHom.id F E) (x : E) :
    algebraMap F E (Algebra.trace F E x) = x + σ x := by
  classical
  haveI : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h2
  let τ : E ≃ₐ[F] E := AlgEquiv.ofBijective σ (Algebra.IsAlgebraic.algHom_bijective σ)
  have hτ : τ ≠ 1 := by
    intro h
    apply hσ
    ext y
    have := congrArg (fun f : E ≃ₐ[F] E => f y) h
    simpa [τ] using this
  have huniv : (Finset.univ : Finset (E ≃ₐ[F] E)) = {1, τ} := by
    symm
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, h2,
      Finset.card_pair (Ne.symm hτ)]
  rw [trace_eq_sum_automorphisms, huniv, Finset.sum_pair (Ne.symm hτ)]
  simp [τ]

open NumberField IsDedekindDomain MeasureTheory Matrix in
open scoped TensorProduct ENNReal nonZeroDivisors Classical in
private theorem ne_id_of_embedding_conj {F E : Type} [Field F] [Field E] [NumberField E] [Algebra F E]
    (hE : IsTotallyComplex E) (σ : E →ₐ[F] E)
    (hσ : ∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x)) :
    σ ≠ AlgHom.id F E := by
  intro h
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  have hc := hE.isComplex w
  rw [InfinitePlace.isComplex_iff] at hc
  apply hc
  rw [ComplexEmbedding.isReal_iff]
  ext x
  have := hσ w.embedding x
  rw [h] at this
  simpa [ComplexEmbedding.conjugate_coe_eq] using this.symm

open NumberField IsDedekindDomain MeasureTheory Matrix in
open scoped TensorProduct ENNReal nonZeroDivisors Classical in

theorem _root_.GlobalTheory.exists_integer_add_conj_eq_one_of_formallyUnramified :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
      (σ : E →ₐ[F] E), _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ → Algebra.FormallyUnramified (𝓞 F) (𝓞 E) →
      ∃ θ : 𝓞 E, (θ : E) + σ θ = 1 := by
  intro F E _ _ _ _ _ σ hCM hU
  obtain ⟨-, hE, h2, hσ⟩ := hCM
  have hD := (_root_.GlobalTheory.formallyUnramified_ringOfIntegers_iff_differentIdeal_eq_top F E).1 hU
  have hdual : FractionalIdeal.dual (𝓞 F) F (1 : FractionalIdeal (𝓞 E)⁰ E) = 1 := by
    have := coeIdeal_differentIdeal (𝓞 F) F E (𝓞 E)
    rw [hD, FractionalIdeal.coeIdeal_top] at this
    exact inv_eq_one.mp this.symm
  have key : ∀ a : F, (∀ b : 𝓞 E, a * Algebra.trace F E (algebraMap (𝓞 E) E b) ∈ (algebraMap (𝓞 F) F).range) →
      a ∈ (algebraMap (𝓞 F) F).range := by
    intro a ha
    have hmem : algebraMap F E a ∈ FractionalIdeal.dual (𝓞 F) F (1 : FractionalIdeal (𝓞 E)⁰ E) := by
      rw [FractionalIdeal.mem_dual (fun h => by
        simpa using congrArg (fun J : FractionalIdeal (𝓞 E)⁰ E => (1 : E) ∈ J) h)]
      intro y hy
      obtain ⟨b, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hy
      rw [Algebra.traceForm_apply, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]
      exact ha b
    rw [hdual] at hmem
    obtain ⟨b, hb⟩ := (FractionalIdeal.mem_one_iff _).1 hmem
    have hint : IsIntegral ℤ (algebraMap F E a) := by
      rw [← hb]
      exact b.isIntegral_coe
    have hint' : IsIntegral ℤ a :=
      (isIntegral_algebraMap_iff (algebraMap F E).injective).1 hint
    exact ⟨⟨a, hint'⟩, rfl⟩
  set I : Ideal (𝓞 F) := LinearMap.range (Algebra.intTrace (𝓞 F) (𝓞 E)) with hI
  have hItop : I = ⊤ := by
    by_contra hne
    obtain ⟨p, hp, hIp⟩ := Ideal.exists_le_maximal I hne
    have hp0 : p ≠ ⊥ := (Ideal.bot_lt_of_maximal p (RingOfIntegers.not_isField F)).ne'
    obtain ⟨x, hx, hx1⟩ := FractionalIdeal.exists_notMem_one_of_ne_bot (K := F) hp0 hp.ne_top
    apply hx1
    obtain ⟨r, hr⟩ := key x (by
      intro b
      have ht : Algebra.intTrace (𝓞 F) (𝓞 E) b ∈ p := hIp ⟨b, rfl⟩
      have hmem := (FractionalIdeal.mem_inv_iff (FractionalIdeal.coeIdeal_ne_zero.mpr hp0)).1 hx
        _ (FractionalIdeal.mem_coeIdeal_of_mem (𝓞 F)⁰ ht)
      obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).1 hmem
      refine ⟨r, ?_⟩
      rw [hr, Algebra.algebraMap_intTrace (K := F) (L := E)])
    rw [← hr]
    exact (FractionalIdeal.mem_one_iff _).2 ⟨r, rfl⟩
  have h1 : (1 : 𝓞 F) ∈ I := hItop ▸ Submodule.mem_top
  obtain ⟨θ, hθ⟩ := h1
  refine ⟨θ, ?_⟩
  rw [← algebraMap_trace_eq_add_of_ne_id h2 σ (ne_id_of_embedding_conj hE σ hσ)]
  have := Algebra.algebraMap_intTrace (A := 𝓞 F) (K := F) (L := E) (B := 𝓞 E) θ
  rw [hθ, map_one] at this
  rw [← this]
  exact map_one _

end GlobalTheory
