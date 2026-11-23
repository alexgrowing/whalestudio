import Mathlib

open Matrix Filter Topology
open scoped BigOperators ComplexOrder

namespace GlobalTheory.CompanionTheory.QuotPrime

theorem exists_surjective_zmod_of_ne_top (X : Type*) [AddCommGroup X] [Module.Finite ℤ X]
    (Y : AddSubgroup X) (hY : Y ≠ ⊤) :
    ∃ (l : ℕ) (_ : l.Prime) (ψ : X →+ ZMod l), Function.Surjective ψ ∧ ∀ y ∈ Y, ψ y = 0 := by
  have hY' : Y.toIntSubmodule ≠ ⊤ := by
    intro h
    apply hY
    rw [eq_top_iff]
    intro x _
    have : x ∈ Y.toIntSubmodule := by rw [h]; trivial
    exact this
  obtain ⟨M, hM, hYM⟩ := (eq_top_or_exists_le_coatom Y.toIntSubmodule).resolve_left hY'
  have hs : IsSimpleModule ℤ (X ⧸ M) := isSimpleModule_iff_isCoatom.2 hM
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.1 hs
  obtain ⟨p, rfl⟩ : ∃ p : ℤ, I = Ideal.span {p} := ⟨_, (Ideal.span_singleton_generator I).symm⟩
  have hp0 : p ≠ 0 := by
    rintro rfl
    have h : (⊥ : Ideal ℤ).IsMaximal := by simpa using hI
    exact Int.not_isField (Ring.isField_iff_maximal_bot.2 h)
  have hp : Prime p := (Ideal.span_singleton_prime hp0).1 hI.isPrime
  refine ⟨p.natAbs, Int.prime_iff_natAbs_prime.1 hp,
    ((Int.quotientSpanEquivZMod p).toAddEquiv.toAddMonoidHom.comp
      e.toAddEquiv.toAddMonoidHom).comp M.mkQ.toAddMonoidHom, ?_, ?_⟩
  · exact ((Int.quotientSpanEquivZMod p).surjective.comp e.surjective).comp M.mkQ_surjective
  · intro y hy
    have h0 : M.mkQ y = 0 := (Submodule.Quotient.mk_eq_zero M).2 (hYM hy)
    change (Int.quotientSpanEquivZMod p) (e (M.mkQ y)) = 0
    rw [h0, map_zero, map_zero]

theorem exists_surjective_zmod_of_ne_zero :
    ∀ (k X : Type) [Field k] [AddCommGroup X] [Module.Finite ℤ X] (Y : AddSubgroup X)
      (δ : X →+ k), δ ≠ 0 → (∀ y ∈ Y, δ y = 0) →
      ∃ (l : ℕ) (_ : l.Prime) (ψ : X →+ ZMod l), Function.Surjective ψ ∧ ∀ y ∈ Y, ψ y = 0 := by
  intro k X _ _ _ Y δ hδ hY
  refine exists_surjective_zmod_of_ne_top X Y ?_
  rintro rfl
  exact hδ (AddMonoidHom.ext fun x => hY x trivial)

end GlobalTheory.CompanionTheory.QuotPrime
