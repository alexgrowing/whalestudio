import Mathlib
import GroundTheory.AutomorphicForms.QuadraticConj
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Theta

open NumberField GroundTheory.Automorphic

section Datum

variable (F E : Type*) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E]
  [IsTotallyComplex E] [Algebra F E] [Algebra.IsQuadraticExtension F E]

include F in

theorem isCMField : IsCMField E := IsCMField.ofCMExtension F E

noncomputable def complexConjOver : E ≃ₐ[F] E :=
  haveI := isCMField F E
  AlgEquiv.ofRingEquiv (f := (IsCMField.complexConj E).toRingEquiv) fun x => by
    have h : ((CMExtension.equivMaximalRealSubfield F E x : maximalRealSubfield E) : E) =
        algebraMap F E x := CMExtension.equivMaximalRealSubfield_apply F E x
    rw [← h]
    exact IsCMField.complexConj_apply_eq_self E _

theorem complexConjOver_apply (x : E) :
    haveI := isCMField F E
    complexConjOver F E x = IsCMField.complexConj E x := rfl

variable {F E}

theorem exists_not_mem_range : ∃ x : E, x ∉ Set.range (algebraMap F E) := by
  by_contra hall
  push Not at hall
  have hsurj : Function.Surjective (Algebra.linearMap F E) := fun x => hall x
  have h1 := LinearMap.finrank_range_le (Algebra.linearMap F E)
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self,
    Algebra.IsQuadraticExtension.finrank_eq_two] at h1
  omega

theorem mem_range_of_conj_eq {x : E} (hx : conj F E x = x) :
    x ∈ Set.range (algebraMap F E) := by
  refine ⟨Algebra.trace F E x / 2, ?_⟩
  have h2 := add_conj (F := F) x
  rw [hx] at h2
  rw [map_div₀, ← h2, map_ofNat]
  field_simp
  ring

variable (F E)

theorem conj_ne_one : conj F E ≠ 1 := by
  intro h
  obtain ⟨x, hx⟩ := exists_not_mem_range (F := F) (E := E)
  exact hx (mem_range_of_conj_eq (by rw [h]; rfl))

theorem conj_eq_complexConj (x : E) :
    haveI := isCMField F E
    conj F E x = IsCMField.complexConj E x := by
  haveI := isCMField F E
  have hcard : Nat.card (E ≃ₐ[F] E) = 2 := by
    rw [IsGalois.card_aut_eq_finrank, Algebra.IsQuadraticExtension.finrank_eq_two]
  have hσ : complexConjOver F E ≠ 1 := by
    intro h
    apply IsCMField.complexConj_ne_one E
    ext y
    have := congrArg (fun g : E ≃ₐ[F] E => g y) h
    simpa [complexConjOver_apply] using this
  have huniq := (Nat.card_eq_two_iff' (1 : E ≃ₐ[F] E)).1 hcard
  have := huniq.unique (conj_ne_one F E) hσ
  rw [this, complexConjOver_apply]

theorem embedding_conj (φ : E →+* ℂ) (x : E) : φ (conj F E x) = starRingEnd ℂ (φ x) := by
  haveI := isCMField F E
  rw [conj_eq_complexConj, IsCMField.complexEmbedding_complexConj]

theorem embedding_algebraMap_conj (φ : E →+* ℂ) (c : F) :
    starRingEnd ℂ (φ (algebraMap F E c)) = φ (algebraMap F E c) := by
  rw [← embedding_conj F E, conj_algebraMap]

variable {F E}

theorem ringHom_ext_of_not_mem {R : Type*} [CommRing R] {x : E}
    (hx : x ∉ Set.range (algebraMap F E)) {φ ψ : E →+* R}
    (hF : ∀ c, φ (algebraMap F E c) = ψ (algebraMap F E c)) (hxe : φ x = ψ x) : φ = ψ := by
  ext y
  rw [← (basisOneOf hx).sum_repr y, Fin.sum_univ_two, basisOneOf_zero, basisOneOf_one,
    Algebra.smul_def, Algebra.smul_def]
  simp only [map_add, map_mul, hF, hxe, map_one]

variable (F E)

theorem eq_or_eq_conjugate_of_comp_eq (φ ψ : E →+* ℂ)
    (h : φ.comp (algebraMap F E) = ψ.comp (algebraMap F E)) :
    ψ = φ ∨ ψ = ComplexEmbedding.conjugate φ := by
  obtain ⟨a, ha⟩ := exists_not_mem_range (F := F) (E := E)
  have hF : ∀ c, φ (algebraMap F E c) = ψ (algebraMap F E c) := fun c =>
    congrArg (fun f : F →+* ℂ => f c) h
  have hquad : ∀ χ : E →+* ℂ, χ a * χ a - χ (algebraMap F E (Algebra.trace F E a)) * χ a +
      χ (algebraMap F E (Algebra.norm F a)) = 0 := by
    intro χ
    rw [← mul_conj (F := F) a, ← add_conj (F := F) a]
    simp only [map_mul, map_add]
    ring
  have hφ := hquad φ
  have hψ := hquad ψ
  rw [← hF, ← hF] at hψ
  have hfac : (ψ a - φ a) * (ψ a - (φ (algebraMap F E (Algebra.trace F E a)) - φ a)) = 0 := by
    linear_combination hψ - hφ
  rcases mul_eq_zero.1 hfac with h1 | h1
  · left
    exact (ringHom_ext_of_not_mem ha hF (sub_eq_zero.1 h1).symm).symm
  · right
    symm
    refine ringHom_ext_of_not_mem ha (fun c => ?_) ?_
    · rw [ComplexEmbedding.conjugate_coe_eq, embedding_algebraMap_conj, hF]
    · rw [ComplexEmbedding.conjugate_coe_eq, ← embedding_conj F E, sub_eq_zero.1 h1, conj_apply,
        map_sub]

theorem eq_or_eq_conjugate_of_mk_eq (φ ψ : E →+* ℂ)
    (h : InfinitePlace.mk (φ.comp (algebraMap F E)) = InfinitePlace.mk (ψ.comp (algebraMap F E))) :
    ψ = φ ∨ ψ = ComplexEmbedding.conjugate φ := by
  refine eq_or_eq_conjugate_of_comp_eq F E φ ψ ?_
  rcases InfinitePlace.mk_eq_iff.1 h with h' | h'
  · exact h'
  · rw [← h']
    ext c
    simp only [ComplexEmbedding.conjugate_coe_eq, RingHom.coe_comp, Function.comp_apply]
    exact (embedding_algebraMap_conj F E φ c).symm

theorem exists_embedding_over (v : InfinitePlace F) :
    ∃ φ : E →+* ℂ, InfinitePlace.mk (φ.comp (algebraMap F E)) = v := by
  obtain ⟨w, hw⟩ := InfinitePlace.comap_surjective (k := F) (K := E) v
  refine ⟨w.embedding, ?_⟩
  rw [← InfinitePlace.comap_mk, InfinitePlace.mk_embedding]
  exact hw

omit [NumberField F] in
variable {F} in

theorem isReal_place (v : InfinitePlace F) : v.IsReal := IsTotallyReal.isReal v

end Datum

end GroundTheory.Heights₂.Theta
