import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledIntegerPeriodic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRightMemSB
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit GlobalTheory.GJReg
open Classical

namespace GlobalTheory.GJReg.FinReps

theorem finite_reps_intM : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (t : k),
    t ≠ 0 → valuation k t < 1 → ∀ N M : ℕ, ∃ R : Finset (Matrix (Fin n) (Fin n) k),
      (∀ Y ∈ R, t ^ N • Y ∈ intM k (Fin n) (Fin n)) ∧
      ∀ X, t ^ N • X ∈ intM k (Fin n) (Fin n) → ∃ Y ∈ R, ∃ E ∈ intM k (Fin n) (Fin n), X = Y + t ^ M • E := by
  intro k _ _ _ _ n t ht _ N M
  have hN : t ^ N ≠ 0 := pow_ne_zero _ ht
  have hM : t ^ M ≠ 0 := pow_ne_zero _ ht
  set I : Set (Matrix (Fin n) (Fin n) k) := intM k (Fin n) (Fin n) with hI
  have hIc : IsCompact I := isCompact_intMatrix (k := k) (m := Fin n) (n := Fin n)
  have hIo : IsOpen I := isOpen_intMatrix (k := k) (m := Fin n) (n := Fin n)
  set S : Set (Matrix (Fin n) (Fin n) k) := {X | t ^ N • X ∈ I} with hS
  have hSimg : S = (fun X => (t ^ N)⁻¹ • X) '' I := by
    ext X; constructor
    · intro hX; exact ⟨t ^ N • X, hX, by simp [smul_smul, inv_mul_cancel₀ hN]⟩
    · rintro ⟨E, hE, rfl⟩; show t ^ N • (t ^ N)⁻¹ • E ∈ I; simpa [smul_smul, mul_inv_cancel₀ hN] using hE
  have hSc : IsCompact S := by rw [hSimg]; exact hIc.image (continuous_const_smul _)
  let U : Matrix (Fin n) (Fin n) k → Set (Matrix (Fin n) (Fin n) k) := fun Y => (fun X => (t ^ M)⁻¹ • (X - Y)) ⁻¹' I
  have hUo : ∀ Y ∈ S, IsOpen (U Y) := fun Y _ => hIo.preimage (by fun_prop : Continuous fun X : Matrix (Fin n) (Fin n) k => (t ^ M)⁻¹ • (X - Y))
  have hcov : S ⊆ ⋃ Y ∈ S, U Y := by
    intro X hX
    refine Set.mem_biUnion hX ?_
    show (t ^ M)⁻¹ • (X - X) ∈ I
    simp only [sub_self, smul_zero]
    intro i j; simp
  obtain ⟨b, hbS, hbf, hsub⟩ := hSc.elim_finite_subcover_image hUo hcov
  refine ⟨hbf.toFinset, fun Y hY => hbS (hbf.mem_toFinset.1 hY), fun X hX => ?_⟩
  obtain ⟨Y, hYb, hXY⟩ := Set.mem_iUnion₂.1 (hsub hX)
  refine ⟨Y, hbf.mem_toFinset.2 hYb, (t ^ M)⁻¹ • (X - Y), hXY, ?_⟩
  rw [smul_smul, mul_inv_cancel₀ hM, one_smul]; abel

end GlobalTheory.GJReg.FinReps
