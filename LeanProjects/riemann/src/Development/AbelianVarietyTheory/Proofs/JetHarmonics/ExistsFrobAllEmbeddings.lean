import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.IsSelfOf
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ImaginaryRootConj

set_option autoImplicit false

noncomputable section

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowAt

def frobKer {R C : Type} [CommRing R] [Field C] (V : VF C) (f : R →+* C) (hf : ∀ x, V.Ge 0 (f x)) : Ideal R where
  carrier := {x | V.MM (f x)}
  add_mem' := fun {a b} ha hb => by
    show 0 < V.v (f (a + b))
    rw [map_add]
    exact V.v.map_lt_add ha hb
  zero_mem' := by
    show 0 < V.v (f 0)
    rw [map_zero, V.v.map_zero]
    exact WithTop.coe_lt_top (0 : ℝ)
  smul_mem' := fun a b hb => by
    show 0 < V.v (f (a * b))
    rw [map_mul, V.v.map_mul]
    exact lt_of_lt_of_le hb (le_add_of_nonneg_left (hf a))

theorem frobKer_isPrime {R C : Type} [CommRing R] [Field C] (V : VF C) (f : R →+* C) (hf : ∀ x, V.Ge 0 (f x)) :
    (frobKer V f hf).IsPrime where
  ne_top' := by
    rw [Ideal.ne_top_iff_one]
    show ¬ 0 < V.v (f 1)
    rw [map_one, V.v.map_one]
    exact lt_irrefl _
  mem_or_mem' := fun {a b} h => by
    have h' : 0 < V.v (f (a * b)) := h
    rw [map_mul, V.v.map_mul] at h'
    by_contra hn
    push_neg at hn
    have h1 : V.v (f a) ≤ 0 := not_lt.1 hn.1
    have h2 : V.v (f b) ≤ 0 := not_lt.1 hn.2
    exact absurd (add_nonpos h1 h2) (not_le.2 h')

theorem exists_frob_of_hom {E C : Type} [Field E] [NumberField E] [IsGalois ℚ E] [Field C] (V : VF C)
    (f : 𝓞 E →+* C) (hf : ∀ x, V.Ge 0 (f x)) :
    ∃ φ : E ≃ₐ[ℚ] E, ∀ x : 𝓞 E, V.MM (f (φ • x) - f x ^ V.l) := by
  set P := frobKer V f hf with hP
  haveI : P.IsPrime := frobKer_isPrime V f hf
  have hl : ((V.l : ℕ) : 𝓞 E) ∈ P := by
    show 0 < V.v (f _)
    rw [map_natCast, V.v_l]
    exact zero_lt_one
  have hP0 : P ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hl
    exact V.l_prime.ne_zero (by exact_mod_cast hl)
  haveI : Finite (𝓞 E ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient hP0
  have hu : P.under ℤ = Ideal.span {(V.l : ℤ)} := by
    have hmax : (Ideal.span {(V.l : ℤ)}).IsMaximal :=
      ((Ideal.span_singleton_prime (by exact_mod_cast V.l_prime.ne_zero)).2
        (Nat.prime_iff_prime_int.1 V.l_prime)).isMaximal (by
          rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast V.l_prime.ne_zero)
    refine (hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_).symm
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
    exact hl
  obtain ⟨φ, hφ⟩ := IsArithFrobAt.exists_of_isInvariant ℤ (E ≃ₐ[ℚ] E) P
  refine ⟨φ, fun x => ?_⟩
  have h := hφ x
  rw [hu, Int.card_ideal_quot] at h
  have h' : V.MM (f (φ • x - x ^ V.l)) := h
  rwa [map_sub, map_pow] at h'

theorem exists_aut_comp_eq {E : Type} [Field E] [NumberField E] [IsGalois ℚ E] (τ₀ τ : E →+* ℂ) :
    ∃ σ : E ≃ₐ[ℚ] E, τ = τ₀.comp (σ : E →+* E) := by
  obtain ⟨σ, hσ⟩ := NumberField.ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := ℚ) τ₀ τ (Subsingleton.elim _ _)
  exact ⟨σ.symm, hσ.symm⟩

theorem exists_frob_all_embeddings : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (lv : Level H) (c : Coeff lv) (T : CDVR) (io : c.F →+* T.Fr) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → IsGalois ℚ E → (∀ σ σ' : E ≃ₐ[ℚ] E, σ * σ' = σ' * σ) → ∃ φ : E ≃ₐ[ℚ] E, ∀ (τ : E →+* ℂ) (x : 𝓞 E), V.MM (emA3 io ι (τ.comp (φ : E →+* E)) x - emA3 io ι τ x ^ V.l) := by
  intro E _ _ _ H lv c T io C _ _ V ι hι hG hab
  obtain ⟨τ₀⟩ : Nonempty (E →+* ℂ) := inferInstance
  have key : ∀ (τ : E →+* ℂ) (s : E ≃ₐ[ℚ] E) (x : 𝓞 E),
      emA3 io ι (τ.comp (s : E →+* E)) x = emA3 io ι τ (s • x) := fun τ s x => rfl
  obtain ⟨φ, hφ⟩ := exists_frob_of_hom V (emA3 io ι τ₀)
    (fun x => GlobalTheory.RowChartCounterexample.em_int_holds τ₀ x hι)
  refine ⟨φ, fun τ x => ?_⟩
  obtain ⟨σ, rfl⟩ := exists_aut_comp_eq τ₀ τ
  rw [key, key, key, ← mul_smul, hab, mul_smul]
  exact hφ _

end GlobalTheory.RowAt
