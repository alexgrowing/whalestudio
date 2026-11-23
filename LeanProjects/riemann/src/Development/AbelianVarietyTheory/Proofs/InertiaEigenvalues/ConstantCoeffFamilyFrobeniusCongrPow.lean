import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffOfW
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

section
variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {O : Type} [CommRing O] [Algebra ℤ_[l] O]
  (t : Wq l a →ₐ[ℤ_[l]] O) (K : Type) [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  (e : ℕ)

theorem cstW_mem_QSet_of_const (c : Wq l a) : cstW t K c ∈ QSet t K e := by
  refine ⟨fun p => if p = (0, 0) then c else 0, ?_⟩
  funext τ
  ext i n
  rw [coeff_ofW]
  simp only [cstW, coeff_C]
  by_cases hi : i = 0
  · by_cases hn : n = 0
    · simp [hi, hn, dpDen]
    · simp [hi, hn, coeff_C]
  · simp [hi]

theorem exists_sigma_eq_pow_add (c : Wq l a) : ∃ d : Wq l a, sigma l a c = c ^ l + (l : Wq l a) * d := by
  have h : sigma l a c - c ^ l ∈ Ideal.span {(l : Wq l a)} := by
    rw [← WittVector.ker_constantCoeff, RingHom.mem_ker, map_sub, map_pow, WittVector.constantCoeff_apply,
      WittVector.constantCoeff_apply, coeff_sigma, sub_self]
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.1 h
  exact ⟨d, by rw [← hd]; ring⟩

end

theorem cstW_mem_GoodSet : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ f : K⟦X⟧, φ₂ (C f) = C (frob K l f)) → φ₂ X = (C X + X) ^ l - C (X ^ l) → ∀ c : Wq l a, cstW t K c ∈ GoodSet t e φ₂ := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ t φ₂ hC _ c
  have h1 : frob2 φ₂ (cstW t K c) = cstW t K (sigma l a c) := by
    funext τ
    change φ₂ (cstW t K c (τ - 1)) = _
    simp only [cstW]
    rw [hC, frob_C, emb_sigma]
  refine ⟨cstW_mem_QSet_of_const t K e c, h1 ▸ cstW_mem_QSet_of_const t K e _, ?_⟩
  obtain ⟨d, hd⟩ := exists_sigma_eq_pow_add c
  refine ⟨cstW t K d, cstW_mem_QSet_of_const t K e d, ?_⟩
  rw [h1, hd]
  funext τ
  simp [cstW]

end GlobalTheory.CrysPrism
