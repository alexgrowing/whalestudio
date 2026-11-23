import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteIsAlgClosedCExt
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.Ex

theorem exists_complete_isAlgClosed_powerSeries :
    ∀ (O' : Type) [CommRing O'] [IsDomain O'] (K : Type) [Field K] [Algebra (PowerSeries O') K] [FaithfulSMul (PowerSeries O') K] [Algebra.IsAlgebraic (PowerSeries O') K], ∃ (C : Type) (_ : NontriviallyNormedField C) (_ : IsUltrametricDist C) (_ : CompleteSpace C) (_ : IsAlgClosed C) (_ : Algebra (FractionRing O') C) (gam : K →+* C) (u : Cˣ), (∀ x, algebraMap (FractionRing O') C (algebraMap O' _ x) = gam (algebraMap (PowerSeries O') K (PowerSeries.C x))) ∧ (∀ r, ‖gam (algebraMap (PowerSeries O') K r)‖ ≤ 1) ∧ (u : C) = gam (algebraMap (PowerSeries O') K PowerSeries.X) ∧ ‖(u : C)‖ < 1 := by
  intro O' _ _ K _ _ _ _
  obtain ⟨C, i1, i2, i3, i4, i5, -, -, hle, hlt⟩ :=
    exists_complete_isAlgClosed_cExt (PowerSeries (FractionRing O'))
      (FractionRing (PowerSeries (FractionRing O')))
  let ψ : PowerSeries (FractionRing O') →+* C :=
    (algebraMap (FractionRing (PowerSeries (FractionRing O'))) C).comp
      (algebraMap (PowerSeries (FractionRing O')) _)
  have hψ : Function.Injective ψ :=
    (algebraMap (FractionRing (PowerSeries (FractionRing O'))) C).injective.comp
      (IsFractionRing.injective (PowerSeries (FractionRing O')) (FractionRing (PowerSeries (FractionRing O'))))
  let φ : PowerSeries O' →+* C := ψ.comp (PowerSeries.map (algebraMap O' (FractionRing O')))
  have hφ : Function.Injective φ :=
    hψ.comp (PowerSeries.map_injective _ (IsFractionRing.injective O' (FractionRing O')))
  let _ : Algebra (PowerSeries O') C := φ.toAlgebra
  have : FaithfulSMul (PowerSeries O') C := (faithfulSMul_iff_algebraMap_injective _ _).2 hφ
  let g : K →ₐ[PowerSeries O'] C := IsAlgClosed.lift
  have hg : ∀ r, g.toRingHom (algebraMap (PowerSeries O') K r) = φ r := fun r => g.commutes r
  have hX : φ PowerSeries.X ≠ 0 := fun h =>
    PowerSeries.X_ne_zero (hφ (h.trans (map_zero φ).symm))
  refine ⟨C, i1, i2, i3, i4, (ψ.comp PowerSeries.C).toAlgebra, g.toRingHom, Units.mk0 _ hX,
    fun x => ?_, fun r => ?_, (hg _).symm, ?_⟩
  · rw [hg]
    change ψ (PowerSeries.C _) = ψ (PowerSeries.map _ _)
    rw [PowerSeries.map_C]
  · rw [hg]
    exact hle _
  · change ‖ψ (PowerSeries.map _ PowerSeries.X)‖ < 1
    rw [PowerSeries.map_X]
    refine hlt _ ?_
    rw [PowerSeries.maximalIdeal_eq_span_X]
    exact Ideal.mem_span_singleton_self _

end GlobalTheory.Ex
