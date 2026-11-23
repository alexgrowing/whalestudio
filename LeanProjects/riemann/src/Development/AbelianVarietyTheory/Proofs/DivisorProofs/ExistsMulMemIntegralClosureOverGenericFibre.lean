import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureFiniteEtale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFreeOver
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.KeyOriginNoeth

theorem exists_common_multiple_mem_closure :
    ∀ (A R : Type) [CommRing A] [IsDomain A] [CommRing R] [Algebra A R]
    (D : Type) [CommRing D] [Algebra (GlobalTheory.LocAcyc.GenFib A R) D]
    [Module.Finite (GlobalTheory.LocAcyc.GenFib A R) D] (s : Finset D),
    ∃ a : A, a ≠ 0 ∧ ∀ d ∈ s,
      GlobalTheory.KeyOriginNoeth.baseHom A R D (algebraMap A R a) * d ∈ GlobalTheory.KeyOriginNoeth.closure A R D := by
  intro A R _ _ _ _ D _ _ _ s
  classical
  letI : Algebra R D := (baseHom A R D).toAlgebra
  haveI : IsScalarTower R (GlobalTheory.LocAcyc.GenFib A R) D :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have key : ∀ d : D, ∃ a : A, a ≠ 0 ∧ IsIntegral R (baseHom A R D (algebraMap A R a) * d) := by
    intro d
    have hd : IsIntegral (GlobalTheory.LocAcyc.GenFib A R) d := Algebra.IsIntegral.isIntegral d
    obtain ⟨⟨m, hm⟩, hmi⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
      (Algebra.algebraMapSubmonoid R (nonZeroDivisors A)) (Rₘ := GlobalTheory.LocAcyc.GenFib A R) d hd
    obtain ⟨a, ha, rfl⟩ := hm
    refine ⟨a, nonZeroDivisors.ne_zero ha, ?_⟩
    exact hmi
  have hmem : ∀ x : D, IsIntegral R x → x ∈ closure A R D := fun x hx => hx
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, by simp⟩
  | insert d s hds ih =>
    obtain ⟨a₂, ha₂, h₂⟩ := ih
    obtain ⟨a₁, ha₁, h₁⟩ := key d
    refine ⟨a₁ * a₂, mul_ne_zero ha₁ ha₂, ?_⟩
    intro e he
    apply hmem
    rw [Finset.mem_insert] at he
    rcases he with rfl | he
    · have : baseHom A R D (algebraMap A R (a₁ * a₂)) * e =
          algebraMap R D (algebraMap A R a₂) * (baseHom A R D (algebraMap A R a₁) * e) := by
        simp only [map_mul]; show _ = baseHom A R D _ * _; ring
      rw [this]
      exact isIntegral_algebraMap.mul h₁
    · have : baseHom A R D (algebraMap A R (a₁ * a₂)) * e =
          algebraMap R D (algebraMap A R a₁) * (baseHom A R D (algebraMap A R a₂) * e) := by
        simp only [map_mul]; show _ = baseHom A R D _ * _; ring
      rw [this]
      exact isIntegral_algebraMap.mul (h₂ e he)

end GlobalTheory.KeyOriginNoeth
