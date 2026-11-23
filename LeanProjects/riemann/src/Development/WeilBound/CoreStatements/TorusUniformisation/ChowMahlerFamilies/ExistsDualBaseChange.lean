import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateFreeIntegralModelsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyCoordIdealStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionEmbeddingGeometricPointsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HTChartExistsHoldsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFiniteBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueEquiv
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueAct
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.Xgn.DualBaseChange

theorem dual_isBaseChange {R : Type} [CommRing R] {A : Type} [Field A] [Algebra R A]
    [IsFractionRing R A] {V : Type} [AddCommGroup V] [Module R V] [Module.Finite R V]
    [Module.Projective R V] {W : Type} [AddCommGroup W] [Module R W] [Module A W]
    [IsScalarTower R A W] {j : V →ₗ[R] W} (hb : IsBaseChange A j) :
    IsBaseChange A hb.toDual := by
  have : Module.FinitePresentation R V := Module.finitePresentation_of_projective R V
  rw [← isLocalizedModule_iff_isBaseChange (nonZeroDivisors R) A]
  refine ⟨(isLocalizedModule_id (nonZeroDivisors R) (Module.Dual A W) A).map_units, ?_, ?_⟩
  · intro φ
    obtain ⟨h, s, hs⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule
      (nonZeroDivisors R) (Algebra.linearMap R A) ((φ.restrictScalars R) ∘ₗ j)
    refine ⟨(h, s), ?_⟩
    apply hb.algHom_ext
    intro v
    have := LinearMap.congr_fun hs v
    rw [hb.toDual_comp_apply]
    exact this.symm
  · intro u₁ u₂ h
    refine ⟨1, ?_⟩
    congr 1
    ext v
    apply IsFractionRing.injective R A
    rw [← hb.toDual_comp_apply, ← hb.toDual_comp_apply, h]

end PositivityTheory.Xgn.DualBaseChange

theorem PositivityTheory.Xgn.exists_dual_base_change : ∀ (Ω : Type) [Field Ω] (O : Type) [CommRing O] [Algebra O Ω] (R : Subalgebra O Ω) [IsFractionRing R Ω] (L : Type) [AddCommGroup L] [Module R L] [Module.Finite R L] [Module.Projective R L] (Li : Type) [AddCommGroup Li] [Module Ω Li] (toLi : L →ₗ[R] Li), IsBaseChange Ω toLi → ∃ j : Module.Dual R L →ₗ[R] Module.Dual Ω Li, IsBaseChange Ω j ∧ ∀ u v, j u (toLi v) = algebraMap R Ω (u v) := by
  intro Ω _ O _ _ R _ L _ _ _ _ Li _ _ toLi hb
  exact ⟨hb.toDual, PositivityTheory.Xgn.DualBaseChange.dual_isBaseChange hb,
    fun u v => hb.toDual_comp_apply u v⟩
