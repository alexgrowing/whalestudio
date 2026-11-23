import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
open NumberField GlobalTheory.CMVal GlobalTheory.LatJet

namespace GlobalTheory.CMSep

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem pointwise {f g : E →+* ℂ} (h : ∀ x : FR E, f (x : E) = g (x : E)) (x : E) :
    g x = f x ∨ g x = starRingEnd ℂ (f x) := by
  have hs : x + IsCMField.complexConj E x ∈ maximalRealSubfield E := by
    rw [← IsCMField.complexConj_eq_self_iff]; simp [add_comm]
  have hp : x * IsCMField.complexConj E x ∈ maximalRealSubfield E := by
    rw [← IsCMField.complexConj_eq_self_iff]; simp [mul_comm]
  have h1 := h ⟨_, hs⟩
  have h2 := h ⟨_, hp⟩
  simp only [map_add, map_mul, IsCMField.complexEmbedding_complexConj] at h1 h2
  have key : (g x - f x) * (g x - starRingEnd ℂ (f x)) = 0 := by
    linear_combination (-(g x)) * h1 + h2
  rcases mul_eq_zero.mp key with e | e
  · exact Or.inl (sub_eq_zero.mp e)
  · exact Or.inr (sub_eq_zero.mp e)

theorem eq_or_eq_conj {f g : E →+* ℂ} (h : ∀ x : FR E, f (x : E) = g (x : E)) :
    g = f ∨ g = ComplexEmbedding.conjugate f := by
  by_contra hne
  push_neg at hne
  obtain ⟨x, hx⟩ : ∃ x, g x ≠ f x := by
    by_contra hh; push_neg at hh; exact hne.1 (RingHom.ext hh)
  obtain ⟨y, hy⟩ : ∃ y, g y ≠ starRingEnd ℂ (f y) := by
    by_contra hh; push_neg at hh; exact hne.2 (RingHom.ext hh)
  have hx' : g x = starRingEnd ℂ (f x) := (pointwise h x).resolve_left hx
  have hy' : g y = f y := (pointwise h y).resolve_right hy
  rcases pointwise h (x + y) with e | e
  · simp only [map_add] at e; exact hx (by linear_combination e - hy')
  · simp only [map_add] at e; exact hy (by linear_combination e - hx')

end GlobalTheory.CMSep

namespace GlobalTheory.CMSep

theorem exists_int_ne : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) (φ : I → E →+* ℂ), IsCMType φ →
    ∀ i k, i ≠ k → ∃ a : 𝓞 (FR E), φ i ((a : FR E) : E) ≠ φ k ((a : FR E) : E) := by
  intro E _ _ _ I φ hφ i k hik
  by_contra hall
  push_neg at hall
  have hext : ((φ i).comp (algebraMap (FR E) E)) = ((φ k).comp (algebraMap (FR E) E)) := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 (FR E)))
    ext a
    exact hall a
  have hres : ∀ x : FR E, φ i (x : E) = φ k (x : E) := fun x => RingHom.congr_fun hext x
  rcases eq_or_eq_conj hres with e | e
  · obtain ⟨j, -, hj⟩ := hφ (φ i)
    have h1 := hj i (Or.inl rfl)
    have h2 := hj k (Or.inl e.symm)
    exact hik (h1.trans h2.symm)
  · obtain ⟨j, -, hj⟩ := hφ (φ k)
    have h1 := hj k (Or.inl rfl)
    have h2 := hj i (Or.inr e)
    exact hik (h2.trans h1.symm)

end GlobalTheory.CMSep
