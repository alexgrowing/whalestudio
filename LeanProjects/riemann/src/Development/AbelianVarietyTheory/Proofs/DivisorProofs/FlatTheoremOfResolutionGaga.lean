import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntBTmulBasis
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

namespace GlobalTheory

theorem exists_left_basis_through_algHom : ∀ (L : Type) [Field L] [NumberField L] (C : Type) [Ring C] [Algebra ℚ C] [FiniteDimensional ℚ C]
    (ι : L →ₐ[ℚ] C), ∃ (r : ℕ) (e : Fin r → C), ∀ x : C, ∃! c : Fin r → L, x = ∑ i, ι (c i) * e i := by
  intro L _ _ C _ _ _ ι
  letI : Module L C := Module.compHom C ι.toRingHom
  have hsmul : ∀ (l : L) (x : C), l • x = ι l * x := fun _ _ => rfl
  haveI : IsScalarTower ℚ L C := ⟨fun q l x => by
    rw [hsmul, hsmul, map_smul, smul_mul_assoc]⟩
  haveI : Module.Finite L C := Module.Finite.of_restrictScalars_finite ℚ L C
  let b := Module.finBasis L C
  refine ⟨Module.finrank L C, b, fun x => ⟨b.repr x, ?_, ?_⟩⟩
  · simp only [← hsmul]
    exact (b.sum_repr x).symm
  · intro c hc
    simp only [← hsmul] at hc
    rw [hc, b.repr_sum_self]

end GlobalTheory
