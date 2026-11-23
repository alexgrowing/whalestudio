import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IsClassFieldHilbert
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.KwRamSplit
import GroundTheory.GlobalFields.TateThesis.Chebotarev
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.CycInertia

open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

theorem UpperTheory.V.CF.kwRamSub :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosed Ω] (L : IntermediateField ℚ Ω) [NumberField L] [IsAbelianGalois ℚ L] (M : ℕ), 0 < M → (∀ p : ℕ, p.Prime → ¬ p ∣ M → UnramAt L p) → ∃ (n : ℕ) (ζ : Ω), IsPrimitiveRoot ζ (M ^ n) ∧ L ≤ ℚ⟮ζ⟯ := by
  intro Ω _ _ _ L _ _ M hM hram
  obtain ⟨n, ⟨g⟩⟩ := kwRam L M hM hram
  haveI : NeZero (M ^ n) := ⟨by positivity⟩
  haveI : NeZero ((M ^ n : ℕ) : ℚ) := ⟨by exact_mod_cast (show M ^ n ≠ 0 by positivity)⟩
  haveI : IsCyclotomicExtension {M ^ n} ℚ (CyclotomicField (M ^ n) ℚ) := by
    convert CyclotomicField.isCyclotomicExtension (M ^ n) ℚ
    · rfl
    · exact Subsingleton.elim _ _
  haveI : NumberField (CyclotomicField (M ^ n) ℚ) :=
    IsCyclotomicExtension.numberField {M ^ n} ℚ _
  have hgal : IsGalois ℚ L := IsAbelianGalois.toIsGalois
  obtain ⟨ξ, hξ⟩ : ∃ z : CyclotomicField (M ^ n) ℚ, IsPrimitiveRoot z (M ^ n) :=
    ⟨_, IsCyclotomicExtension.zeta_spec _ ℚ _⟩
  let ψ : CyclotomicField (M ^ n) ℚ →ₐ[ℚ] Ω := IsAlgClosed.lift
  refine ⟨n, ψ ξ, hξ.map_of_injective ψ.injective, ?_⟩
  have hnorm : (ψ.comp g).fieldRange = L :=
    @AlgHom.fieldRange_of_normal ℚ Ω _ _ _ L
      (by convert hgal.to_normal; all_goals first | rfl | exact Subsingleton.elim _ _) (ψ.comp g)
  rw [← hnorm]
  intro x hx
  obtain ⟨y, rfl⟩ := AlgHom.mem_fieldRange.mp hx
  have hy : g y ∈ Algebra.adjoin ℚ {ξ} := by
    rw [IsCyclotomicExtension.adjoin_primitive_root_eq_top hξ]
    trivial
  have hψ : ψ (g y) ∈ Algebra.adjoin ℚ {ψ ξ} := by
    rw [← Set.image_singleton, ← AlgHom.map_adjoin]
    exact ⟨g y, hy, rfl⟩
  exact IntermediateField.algebra_adjoin_le_adjoin ℚ {ψ ξ} hψ
