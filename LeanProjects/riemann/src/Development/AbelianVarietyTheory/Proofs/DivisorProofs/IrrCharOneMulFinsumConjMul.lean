import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory

theorem exists_sum_conj_eq_smul_one {G V : Type} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) [ρ.IsIrreducible] (x : G) :
    ∃ c : ℂ, ∑ h : G, ρ (h * x * h⁻¹) = c • (1 : Module.End ℂ V) := by
  have hc : ∀ g : G, (∑ h : G, ρ (h * x * h⁻¹)) * ρ g = ρ g * ∑ h : G, ρ (h * x * h⁻¹) := by
    intro g
    rw [Finset.sum_mul, Finset.mul_sum]
    refine (Fintype.sum_equiv (Equiv.mulLeft g) _ _ fun h => ?_).symm
    rw [← map_mul, ← map_mul]
    congr 1
    simp [mul_assoc]
  let T : Representation.IntertwiningMap ρ ρ :=
    { toLinearMap := ∑ h : G, ρ (h * x * h⁻¹)
      isIntertwining' := fun g => hc g }
  obtain ⟨c, hT⟩ := (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
    (ρ := ρ)).2 T
  refine ⟨c, LinearMap.ext fun v => ?_⟩
  change T v = c • v
  rw [← hT, Algebra.algebraMap_eq_smul_one]
  rfl

theorem character_one_mul_sum_conj_mul {G V : Type} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) [ρ.IsIrreducible] (x y : G) :
    ρ.character 1 * ∑ h : G, ρ.character (h * x * h⁻¹ * y)
      = (Fintype.card G : ℂ) * (ρ.character x * ρ.character y) := by
  obtain ⟨c, hc⟩ := exists_sum_conj_eq_smul_one ρ x
  have key : ∀ z : G, ∑ h : G, ρ.character (h * x * h⁻¹ * z) = c * ρ.character z := by
    intro z
    have := congrArg (fun A => LinearMap.trace ℂ V (A * ρ z)) hc
    simp only [Finset.sum_mul, map_sum, smul_mul_assoc, one_mul, map_smul, smul_eq_mul, ← map_mul] at this
    exact this
  have h1 := key 1
  simp only [mul_one, Representation.char_conj, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h1
  rw [key y, ← mul_assoc, mul_comm _ c, ← h1, mul_assoc]

theorem irrChar_one_mul_finsum_conj_mul : ∀ (G : Type) [Group G] [Finite G] (χ : G → ℂ), IsIrrChar ℂ ℂ χ → ∀ x y : G, χ 1 * ∑ᶠ h : G, χ (h * x * h⁻¹ * y) = (Nat.card G : ℂ) * (χ x * χ y) := by
  intro G _ _ χ hχ x y
  let := Fintype.ofFinite G
  obtain ⟨n, ρ, hρ, h⟩ := hχ
  have hh : χ = ρ.character := by
    funext g
    simpa using h g
  subst hh
  rw [finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card]
  exact character_one_mul_sum_conj_mul ρ x y

end GlobalTheory
