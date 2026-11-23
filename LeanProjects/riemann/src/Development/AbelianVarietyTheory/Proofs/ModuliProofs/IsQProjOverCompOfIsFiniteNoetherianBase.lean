import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory

theorem isQProjOver_comp_of_isFinite_general {R : Type} [CommRing R] {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f]
    {s : Y ⟶ Sp R} (h : IsQProjOver s) : IsQProjOver (f ≫ s) := by
  obtain ⟨N, i, hi, hq, rfl⟩ := h
  have hO : IsAmpleLB (ProjSpace.O1 R N) := isAmpleLB_basic.2.2.2.2.2.2.1 R N
  have hY : IsAmpleLB ((ProjSpace.O1 R N).pull i) := hO.pull_of_isImmersion i
  have hX : IsAmpleLB (((ProjSpace.O1 R N).pull i).pull f) := hY.pull_of_isFinite f
  have := isProper_str R N
  have : LocallyOfFiniteType (f ≫ i ≫ PSpace.str R N) := inferInstance
  exact hX.isQProjOver _

theorem isQProjOver_comp_of_isFinite_noetherian :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X Y : Scheme.{0}) (f : X ⟶ Y) (s : Y ⟶ Sp R),
      IsFinite f → IsQProjOver s → IsQProjOver (f ≫ s) := by
  intro R _ _ X Y f s hf h
  exact isQProjOver_comp_of_isFinite_general f h

end GlobalTheory
