import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl

set_option autoImplicit false

noncomputable section

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.AdicCompl

theorem completion_complete (B : Type) [CommRing B] (π : B) :
    IsAdicComplete (Ideal.span {algebraMap B (AdicCompletion (Ideal.span {π}) B) π})
      (AdicCompletion (Ideal.span {π}) B) := by
  have h := AdicCompletion.isAdicComplete (R := B) (I := Ideal.span {π}) (M := B)
    (Submodule.fg_span_singleton _)
  rw [← IsAdicComplete.map_algebraMap_iff (S := AdicCompletion (Ideal.span {π}) B)] at h
  simpa [Ideal.map_span] using h

theorem completion_surj (B : Type) [CommRing B] (π : B) (M : ℕ)
    (y : AdicCompletion (Ideal.span {π}) B) :
    ∃ x : B, y - algebraMap B (AdicCompletion (Ideal.span {π}) B) x ∈
      Ideal.span {algebraMap B (AdicCompletion (Ideal.span {π}) B) π ^ M} := by
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (y.1 M)
  refine ⟨a, ?_⟩
  have hx : y - algebraMap B (AdicCompletion (Ideal.span {π}) B) a ∈
      ((Ideal.span {π}) ^ M).map (algebraMap B (AdicCompletion (Ideal.span {π}) B)) := by
    rw [← Submodule.restrictScalars_mem B, ← Ideal.smul_top_eq_map,
      AdicCompletion.pow_smul_top_eq_ker_eval (Submodule.fg_span_singleton π),
      AdicCompletion.algebraMap_apply]
    simpa [AdicCompletion.eval, sub_eq_zero] using ha.symm
  rwa [Ideal.span_singleton_pow, Ideal.map_span, Set.image_singleton, map_pow] at hx

theorem completion_inj (B : Type) [CommRing B] (π : B) (M : ℕ) (x : B)
    (h : algebraMap B (AdicCompletion (Ideal.span {π}) B) x ∈
      Ideal.span {algebraMap B (AdicCompletion (Ideal.span {π}) B) π ^ M}) :
    x ∈ Ideal.span {π ^ M} := by
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 h
  have h1 := congrArg (AdicCompletion.evalₐ (Ideal.span {π}) M) hz
  have hf : Ideal.Quotient.mk (Ideal.span {π} ^ M) (π ^ M) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (by
      rw [Ideal.span_singleton_pow]; exact Ideal.mem_span_singleton_self _)
  rw [map_mul, map_pow, AlgHom.commutes, ← map_pow, AlgHom.commutes, Ideal.Quotient.algebraMap_eq,
    hf, mul_zero] at h1
  rw [← Ideal.span_singleton_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.1 h1.symm

theorem exists_isCompl : ∀ (B : Type) [CommRing B] (π : B),
    ∃ (T : Type) (_ : CommRing T) (g : B →+* T), IsCompl π g := by
  intro B _ π
  exact ⟨AdicCompletion (Ideal.span {π}) B, inferInstance,
    algebraMap B (AdicCompletion (Ideal.span {π}) B),
    { compl := completion_complete B π
      surj := completion_surj B π
      inj := completion_inj B π }⟩

end GlobalTheory.CompanionTheory.AdicCompl
