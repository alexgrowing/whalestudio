import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinSummandUnitSmul
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

variable {F : Type} [Field F] [NumberField F]

set_option autoImplicit false in
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
variable {F : Type} [Field F] [NumberField F] in
theorem _root_.GlobalTheory.HilbFam.transf_units_smul (T : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F)) (ε : (𝓞 F)ˣ) (x : Fin 2 → F) :
    T (ε • x) = ε • T x := by
  change T.toLinearMap ((ε : 𝓞 F) • x) = (ε : 𝓞 F) • T.toLinearMap x
  exact LinearMap.map_smul_of_tower T.toLinearMap _ _

noncomputable def transfQuot (T : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F)) :
    Quotient (MulAction.orbitRel (𝓞 F)ˣ (Fin 2 → F)) ≃ Quotient (MulAction.orbitRel (𝓞 F)ˣ (Fin 2 → F)) :=
  Quotient.congr T.toEquiv (by
    intro x y
    simp only [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨ε, rfl⟩
      exact ⟨ε, (transf_units_smul T ε y).symm⟩
    · rintro ⟨ε, h⟩
      refine ⟨ε, T.injective ?_⟩
      rw [transf_units_smul]
      exact h)

end GlobalTheory.HilbFam
