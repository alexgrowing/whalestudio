import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.FunctionFieldPrimitive

open Polynomial

open scoped MatrixGroups TensorProduct in
open Matrix in
open Polynomial in

theorem _root_.GlobalTheory.FunctionFieldPrimitive.exists_integral_primitive {F : Type} [Field F] [CharZero F]
    {L : Type} [Field L]
    [Algebra F L] (t : L) (ht : Transcendental F t)
    (hfin : FiniteDimensional (IntermediateField.adjoin F {t}) L) :
    ∃ (Φ : Polynomial (Polynomial F)) (ω : L), Φ.Monic ∧ Irreducible Φ ∧
      Φ.eval₂ (Polynomial.aeval t).toRingHom ω = 0 ∧
      ∀ x : L, ∃ Q : Polynomial F, Q ≠ 0 ∧ ∃ R : Polynomial (Polynomial F),
        Polynomial.aeval t Q * x = R.eval₂ (Polynomial.aeval t).toRingHom ω := by
  have htK : t ∈ IntermediateField.adjoin F {t} := IntermediateField.mem_adjoin_simple_self F t
  have hne : ∀ p : Polynomial F, p ≠ 0 → Polynomial.aeval t p ≠ 0 := fun p hp h =>
    ht ⟨p, hp, h⟩
  have hden : ∀ y ∈ IntermediateField.adjoin F {t}, ∃ s : Polynomial F, s ≠ 0 ∧
      ∃ r : Polynomial F, Polynomial.aeval t s * y = Polynomial.aeval t r := by
    intro y hy
    obtain ⟨r, s, rfl⟩ := (IntermediateField.mem_adjoin_simple_iff F y).1 hy
    by_cases hs : s = 0
    · exact ⟨1, one_ne_zero, 0, by simp [hs]⟩
    · exact ⟨s, hs, r, by rw [mul_div_cancel₀ _ (hne s hs)]⟩
  have hcomm : ∀ p : Polynomial F,
      ((Polynomial.aeval (⟨t, htK⟩ : IntermediateField.adjoin F {t}) p :
        IntermediateField.adjoin F {t}) : L) = Polynomial.aeval t p := fun p =>
    (Polynomial.aeval_algHom_apply (IntermediateField.adjoin F {t}).val
      (⟨t, htK⟩ : IntermediateField.adjoin F {t}) p).symm
  letI algK : Algebra (Polynomial F) (IntermediateField.adjoin F {t}) :=
    (Polynomial.aeval (⟨t, htK⟩ : IntermediateField.adjoin F {t})).toRingHom.toAlgebra
  letI algL : Algebra (Polynomial F) L := (Polynomial.aeval t).toRingHom.toAlgebra
  haveI : IsScalarTower (Polynomial F) (IntermediateField.adjoin F {t}) L :=
    IsScalarTower.of_algebraMap_eq fun p => (hcomm p).symm
  haveI : Algebra.IsAlgebraic (Polynomial F) (IntermediateField.adjoin F {t}) := by
    constructor
    intro k
    obtain ⟨s, hs, r, hsr⟩ := hden k.1 k.2
    refine ⟨Polynomial.C s * Polynomial.X - Polynomial.C r, ?_, ?_⟩
    · intro h
      have h1 := congrArg (fun P => Polynomial.coeff P 1) h
      simp at h1
      exact hs h1
    · apply Subtype.val_injective
      rw [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_C, Polynomial.aeval_X]
      show ((Polynomial.aeval (⟨t, htK⟩ : IntermediateField.adjoin F {t}) s :
          IntermediateField.adjoin F {t}) : L) * k -
        ((Polynomial.aeval (⟨t, htK⟩ : IntermediateField.adjoin F {t}) r :
          IntermediateField.adjoin F {t}) : L) = 0
      rw [hcomm, hcomm, hsr, sub_self]
  haveI : Algebra.IsAlgebraic (IntermediateField.adjoin F {t}) L :=
    Algebra.IsAlgebraic.of_finite _ _
  haveI : Algebra.IsAlgebraic (Polynomial F) L :=
    Algebra.IsAlgebraic.trans (Polynomial F) (IntermediateField.adjoin F {t}) L
  obtain ⟨θ, hθ⟩ := Field.exists_primitive_element (IntermediateField.adjoin F {t}) L
  obtain ⟨y, hy0, hyint⟩ :=
    (Algebra.IsAlgebraic.isAlgebraic (R := Polynomial F) θ).exists_integral_multiple
  have hωdef : y • θ = Polynomial.aeval t y * θ := Algebra.smul_def y θ
  have hyK : Polynomial.aeval t y ∈ IntermediateField.adjoin F {t} := by
    rw [← hcomm]; exact Subtype.property _
  have htop : IntermediateField.adjoin (IntermediateField.adjoin F {t}) {y • θ} = ⊤ := by
    rw [eq_top_iff, ← hθ, IntermediateField.adjoin_simple_le_iff]
    have hθeq : θ = (Polynomial.aeval t y)⁻¹ * (y • θ) := by
      rw [hωdef, inv_mul_cancel_left₀ (hne y hy0)]
    have hmem : (Polynomial.aeval t y)⁻¹ * (y • θ) ∈
        IntermediateField.adjoin (IntermediateField.adjoin F {t}) {y • θ} :=
      mul_mem (inv_mem (IntermediateField.algebraMap_mem _
        (⟨Polynomial.aeval t y, hyK⟩ : IntermediateField.adjoin F {t})))
        (IntermediateField.mem_adjoin_simple_self _ (y • θ))
    rwa [← hθeq] at hmem
  refine ⟨minpoly (Polynomial F) (y • θ), y • θ, minpoly.monic hyint,
    minpoly.irreducible hyint, minpoly.aeval _ _, ?_⟩
  intro x
  have hx : x ∈ Algebra.adjoin (IntermediateField.adjoin F {t}) {y • θ} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic (y • θ)), htop]
    trivial
  induction hx using Algebra.adjoin_induction with
  | mem z hz =>
    rw [Set.mem_singleton_iff.1 hz]
    exact ⟨1, one_ne_zero, Polynomial.X, by simp⟩
  | algebraMap k =>
    obtain ⟨s, hs, r, hsr⟩ := hden k.1 k.2
    exact ⟨s, hs, Polynomial.C r, by rw [Polynomial.eval₂_C]; exact hsr⟩
  | add a b _ _ ha hb =>
    obtain ⟨Q₁, hQ₁, R₁, h₁⟩ := ha
    obtain ⟨Q₂, hQ₂, R₂, h₂⟩ := hb
    refine ⟨Q₁ * Q₂, mul_ne_zero hQ₁ hQ₂, Polynomial.C Q₂ * R₁ + Polynomial.C Q₁ * R₂, ?_⟩
    rw [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_mul, Polynomial.eval₂_C,
      Polynomial.eval₂_C, ← h₁, ← h₂]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_mul]
    ring
  | mul a b _ _ ha hb =>
    obtain ⟨Q₁, hQ₁, R₁, h₁⟩ := ha
    obtain ⟨Q₂, hQ₂, R₂, h₂⟩ := hb
    refine ⟨Q₁ * Q₂, mul_ne_zero hQ₁ hQ₂, R₁ * R₂, ?_⟩
    rw [Polynomial.eval₂_mul, ← h₁, ← h₂, map_mul]
    ring

end GlobalTheory.FunctionFieldPrimitive
