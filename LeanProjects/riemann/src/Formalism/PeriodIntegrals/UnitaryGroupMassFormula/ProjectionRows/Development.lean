import Mathlib
import Formalism.PeriodIntegrals.DivisionRowsRationalLattice
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProjectionRows.ValLeOneOfMemRange

noncomputable section

namespace PI.DvRows

open NumberField IsDedekindDomain Formalism.BasicNotions PI.Dv

def PartB : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [NumberField.IsTotallyComplex K] [IsGalois ℚ K]
    (A : HLat K) (e : Module.End K A.V) (n : ℕ) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K),
    StarIsConj K → IsProj A e n → IsHermE A e h → IsCMFormE A e h →
    (∀ w, DualInAt A h A.L w) → ∀ U : Submodule K A.V, U ≤ LinearMap.range e →
    ∀ γ : HeightOneSpectrum (𝓞 K) → ℤ, (∀ w, IsValG A e h U w (γ w)) →
      degL A (cutE A e A.L ⊓ U.restrictScalars (𝓞 K)) - degL A (cutE A e A.L) ≤
        ∑ᶠ w, lw K w * (γ w : ℝ)

theorem dvProjRows_of (hB : PartB) : PI.Dv.division_rows_base_level := by
  intro K _ _ _ _ _ A e n h hS hP hH hC hD U hU
  exact ⟨fun w k hk => partA A e n h hP hH hD U hU w k hk,
    fun γ hγ => hB K A e n h hS hP hH hC hD U hU γ hγ, partC A e U⟩

end PI.DvRows
