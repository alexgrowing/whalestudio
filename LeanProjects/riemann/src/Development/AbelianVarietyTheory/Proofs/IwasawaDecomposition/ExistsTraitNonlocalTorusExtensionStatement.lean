import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTraitNonlocalTorusExtension
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.GeneratorValues
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_trait_nonlocal_torusExtension' : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G →
    ∀ (W : Type) [CommRing W] [IsLocalRing W] (g : R →+* W), ¬ IsLocalHom g →
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (ψ : R →+* V)
      (Ω : Type) (_ : Field Ω) (α : FractionRing V →+* Ω) (β : W →+* Ω),
      IsLocalHom ψ ∧ (∀ x ∈ maximalIdeal W, β x = 0) ∧
      (α.comp (algebraMap V (FractionRing V))).comp ψ = β.comp g ∧
      Nonempty (TorusExtension ((Over.pullback (spMap ((algebraMap V (FractionRing V)).comp ψ))).obj G)) := by
  first | exact @GlobalTheory.exists_trait_nonlocal_torusExtension | exact GlobalTheory.exists_trait_nonlocal_torusExtension | (intros; apply GlobalTheory.exists_trait_nonlocal_torusExtension <;> assumption)
