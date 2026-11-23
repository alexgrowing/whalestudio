import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LengthEqLengthInvariantsOfTorsionLevels
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.TensSurj
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.TensTors

open scoped TensorProduct
open GlobalTheory.TateLimit

theorem UpperTheory.V.K.tensCard :
    ∀ (l : ℕ) [Fact l.Prime] (H : Type) [AddCommGroup H] [Finite (AddCommGroup.torsion H)] (Y : Submodule ℤ_[l] (ℤ_[l] ⊗[ℤ] H)) [Finite Y], Nat.card Y ≤ Nat.card (AddCommGroup.torsion H) := by
  intro l _ H _ _ Y _
  have hT : AddMonoid.IsTorsion (AddCommGroup.torsion H) := fun t => isOfFinAddOrder_of_finite t
  have key : ∀ y : Y, ∃ t : AddCommGroup.torsion H,
      ((1 : ℤ_[l]) ⊗ₜ[ℤ] (t : H) : ℤ_[l] ⊗[ℤ] H) = (y : ℤ_[l] ⊗[ℤ] H) := by
    intro y
    have hy : IsOfFinAddOrder (y : ℤ_[l] ⊗[ℤ] H) := by
      obtain ⟨n, hn, hny⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1 (isOfFinAddOrder_of_finite y)
      refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨n, hn, ?_⟩
      have := congrArg Y.subtype hny
      rw [map_nsmul, map_zero] at this
      exact this
    obtain ⟨z, hz⟩ := UpperTheory.V.K.tensTors l H _ hy
    obtain ⟨t, rfl⟩ := UpperTheory.V.K.tensSurj l _ hT z
    refine ⟨t, ?_⟩
    rw [← hz, LinearMap.lTensor_tmul]
    rfl
  choose f hf using key
  refine Nat.card_le_card_of_injective f ?_
  intro a b hab
  apply Subtype.ext
  rw [← hf a, ← hf b, hab]
