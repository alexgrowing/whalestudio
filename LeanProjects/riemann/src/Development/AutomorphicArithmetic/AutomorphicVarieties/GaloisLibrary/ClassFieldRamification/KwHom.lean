import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IsClassFieldHilbert
import GroundTheory.GlobalFields.TateThesis.Chebotarev
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.CycInertia
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.Kw

open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

theorem UpperTheory.V.CF.kwHom :
    ∀ (L : Type) [Field L] [NumberField L] [IsAbelianGalois ℚ L], ∃ N : ℕ, 0 < N ∧ Nonempty (L →ₐ[ℚ] CyclotomicField N ℚ) := by
  intro L _ _ _
  let f : L →ₐ[ℚ] AlgebraicClosure ℚ := IsAlgClosed.lift
  let e : L ≃ₐ[ℚ] f.fieldRange := AlgEquiv.ofInjectiveField f
  haveI : IsAbelianGalois ℚ f.fieldRange := IsAbelianGalois.of_algHom e.symm.toAlgHom
  haveI : FiniteDimensional ℚ f.fieldRange := e.toLinearEquiv.finiteDimensional
  obtain ⟨N, ζ, hN, hζ, hle⟩ := UpperTheory.V.CF.kw (AlgebraicClosure ℚ) f.fieldRange
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI hNQ : NeZero ((N : ℕ) : ℚ) := ⟨by exact_mod_cast hN.ne'⟩
  haveI : IsCyclotomicExtension {N} ℚ ℚ⟮ζ⟯ := hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
  haveI hC : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) :=
    @CyclotomicField.isCyclotomicExtension N _ ℚ _ hNQ
  refine ⟨N, hN, ⟨?_⟩⟩
  exact ((IsCyclotomicExtension.algEquiv {N} ℚ ℚ⟮ζ⟯ (CyclotomicField N ℚ)).toAlgHom.comp
    (IntermediateField.inclusion hle)).comp e.toAlgHom
