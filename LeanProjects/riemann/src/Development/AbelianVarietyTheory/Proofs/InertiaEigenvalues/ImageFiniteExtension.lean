import Mathlib

namespace GlobalTheory

theorem exists_finiteDimensional_intermediateField_eq_range_fractionRing
    (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [Algebra ℤ_[l] O]
    [Module.Finite ℤ_[l] O] (ι : FractionRing O →+* PadicAlgCl l)
    (hι : ∀ z : ℤ_[l], ι (algebraMap O (FractionRing O) (algebraMap ℤ_[l] O z)) =
      algebraMap ℚ_[l] (PadicAlgCl l) (z : ℚ_[l])) :
    ∃ L : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] L ∧
      ∀ y, y ∈ L ↔ ∃ a, ι a = y := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ_[l]) (M := O)
  let f : O → PadicAlgCl l := fun o => ι (algebraMap O (FractionRing O) o)
  let S : Set (PadicAlgCl l) := f '' (s : Set O)
  haveI : Finite S := (s.finite_toSet.image f).to_subtype
  have hQ : ∀ x : ℚ_[l], algebraMap ℚ_[l] (PadicAlgCl l) x ∈ ι.fieldRange := by
    intro x
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := ℤ_[l]) x
    rw [map_div₀]
    refine ι.fieldRange.div_mem ⟨_, hι a⟩ ⟨_, hι b⟩
  refine ⟨IntermediateField.adjoin ℚ_[l] S, ?_, ?_⟩
  · exact IntermediateField.finiteDimensional_adjoin
      (fun x _ => (Algebra.IsAlgebraic.isAlgebraic (R := ℚ_[l]) x).isIntegral)
  · have hO : ∀ o : O, f o ∈ IntermediateField.adjoin ℚ_[l] S := by
      intro o
      have ho : o ∈ Submodule.span ℤ_[l] (s : Set O) := by rw [hs]; trivial
      induction ho using Submodule.span_induction with
      | mem x hx => exact IntermediateField.subset_adjoin _ _ ⟨x, hx, rfl⟩
      | zero => simp [f]
      | add x y _ _ hx hy =>
        simp only [f, map_add]
        exact add_mem hx hy
      | smul z x _ hx =>
        simp only [f, Algebra.smul_def, map_mul, hι]
        exact mul_mem (IntermediateField.algebraMap_mem _ _) hx
    intro y
    constructor
    · intro hy
      have hle : IntermediateField.adjoin ℚ_[l] S ≤ ι.fieldRange.toIntermediateField hQ := by
        rw [IntermediateField.adjoin_le_iff]
        rintro _ ⟨o, -, rfl⟩
        exact ⟨_, rfl⟩
      exact hle hy
    · rintro ⟨a, rfl⟩
      obtain ⟨p, q, -, rfl⟩ := IsFractionRing.div_surjective (A := O) a
      rw [map_div₀]
      exact div_mem (hO p) (hO q)

end GlobalTheory
