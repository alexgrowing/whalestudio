import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SecJets4
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ConjInvIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogHeightBoundFromInequalityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLatticeBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiFibrationLieLatticeFullStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetSlopeDegreeInequalityStatement
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.PosSemidefOfForallCombination
import ReciprocityTheory.GeometryOfNumbers.MatrixArithmetic.WeakMatSt
open NumberField MeasureTheory ReciprocityTheory.GeometryOfNumbersTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LieHt
open scoped ComplexOrder

namespace GlobalTheory

theorem embeddings_restrict_fiber_card (K K' : Type) [Field K] [NumberField K] [Field K']
    [NumberField K'] [Algebra K K'] (τ : K →+* ℂ) :
    Nat.card {σ : K' →+* ℂ // σ.comp (algebraMap K K') = τ} = Module.finrank K K' := by
  letI : Algebra K ℂ := τ.toAlgebra
  haveI : FiniteDimensional K K' := Module.Finite.of_restrictScalars_finite ℚ K K'
  have e : {σ : K' →+* ℂ // σ.comp (algebraMap K K') = τ} ≃ (K' →ₐ[K] ℂ) :=
    { toFun := fun σ => { σ.1 with commutes' := fun x => congrArg (fun g : K →+* ℂ => g x) σ.2 }
      invFun := fun φ => ⟨φ.toRingHom, by ext x; exact φ.commutes x⟩
      left_inv := fun σ => by ext; rfl
      right_inv := fun φ => by ext; rfl }
  rw [Nat.card_congr e]
  exact AlgHom.natCard_of_splits K K' ℂ (fun _ => IsAlgClosed.splits _)

theorem sum_embeddings_comp_restrict (K K' : Type) [Field K] [NumberField K] [Field K']
    [NumberField K'] [Algebra K K'] (f : (K →+* ℂ) → ℝ) :
    (∑ σ : K' →+* ℂ, f (σ.comp (algebraMap K K'))) =
      (Module.finrank K K' : ℝ) * ∑ τ : K →+* ℂ, f τ := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ (fun σ : K' →+* ℂ => σ.comp (algebraMap K K'))
    (fun σ => f (σ.comp (algebraMap K K'))), Finset.mul_sum]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [Finset.sum_congr rfl (g := fun _ => f τ) (fun σ hσ => by rw [(Finset.mem_filter.mp hσ).2]),
    Finset.sum_const, nsmul_eq_mul]
  congr 1
  rw [← embeddings_restrict_fiber_card K K' τ, Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem mean_embeddings_comp_restrict (K K' : Type) [Field K] [NumberField K] [Field K']
    [NumberField K'] [Algebra K K'] (f : (K →+* ℂ) → ℝ) :
    (∑ σ : K' →+* ℂ, f (σ.comp (algebraMap K K'))) / (Module.finrank ℚ K' : ℝ) =
      (∑ σ : K →+* ℂ, f σ) / (Module.finrank ℚ K : ℝ) := by
  haveI : FiniteDimensional K K' := Module.Finite.of_restrictScalars_finite ℚ K K'
  rw [sum_embeddings_comp_restrict, ← Module.finrank_mul_finrank ℚ K K']
  have h1 : (Module.finrank K K' : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  have h2 : (Module.finrank ℚ K : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  push_cast
  field_simp

end GlobalTheory
