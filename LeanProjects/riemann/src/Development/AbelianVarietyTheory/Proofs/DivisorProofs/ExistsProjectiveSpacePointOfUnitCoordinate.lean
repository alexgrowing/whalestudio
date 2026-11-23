import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsTwoPoints
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ProjectiveRepresentationPullbackCoordinates

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin

theorem exists_pCrd_of_isUnit : ∀ (o R : Type) [CommRing o] [CommRing R] (n : ℕ) (β : o →+* R) (v : Fin (n + 1) → R),
    (∃ j, IsUnit (v j)) → ∃ ξ : Sp R ⟶ PSpace o n, ξ ≫ PSpace.str o n = spMap β ∧ PCrd ξ v := by
  intro o R _ _ n β v ⟨j, hj⟩
  have hv : Ideal.span (Set.range v) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨j, rfl⟩) hj
  refine ⟨GlobalTheory.ProjSpace.pt β v hv, GlobalTheory.ProjSpace.pt_str β v hv, ?_⟩
  have h1 := (GlobalTheory.ZM.ProjCoord.secCoord_iff (Equiv.refl _) (𝟙 _) β (GlobalTheory.ProjSpace.pt β v hv)
    (by rw [Category.comp_id, GlobalTheory.ProjSpace.pt_str]) v).2 ⟨hv, Category.comp_id _⟩
  have h2 := (GlobalTheory.ZM.RepBC.secCoord_pull (GlobalTheory.ProjSpace.O1 o n) (GlobalTheory.ProjSpace.coord o n) (𝟙 _) _ v).1 h1
  rwa [Category.comp_id] at h2

end GlobalTheory.UMin
