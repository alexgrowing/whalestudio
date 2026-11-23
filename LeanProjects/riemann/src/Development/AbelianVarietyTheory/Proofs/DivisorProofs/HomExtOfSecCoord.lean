import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.IsE8ThetaStructure
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsTwoPoints
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsoOfProjectiveCoordinateRepresentation
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ProjectiveRepresentationPullbackCoordinates
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM
open scoped CategoryTheory.Obj

namespace GlobalTheory.ZM.ProjExt

theorem eq_pt_of_secCoord {o : Type} [CommRing o] {m : ℕ} {A : Type} [CommRing A] (c : o →+* A)
    (y : Sp A ⟶ PSpace o m) (hy : y ≫ PSpace.str o m = spMap c) (v : Fin (m + 1) → A)
    (h : SecCoord (GlobalTheory.ProjSpace.O1 o m) (GlobalTheory.ProjSpace.coord o m) y v) :
    ∃ hv : Ideal.span (Set.range v) = ⊤, y = GlobalTheory.ProjSpace.pt c v hv := by
  have h1 := (RepBC.secCoord_pull (GlobalTheory.ProjSpace.O1 o m) (GlobalTheory.ProjSpace.coord o m) (𝟙 _) y v).2
    (by rwa [Category.comp_id])
  obtain ⟨hv, e⟩ := (ProjCoord.secCoord_iff (Equiv.refl _) (𝟙 _) c y (by rwa [Category.comp_id]) v).1 h1
  exact ⟨hv, (Category.comp_id _).symm.trans e⟩

theorem hom_ext_of_secCoord : ∀ (o : Type) [CommRing o] (Y : Scheme.{0}) (m : ℕ) (g g' : Y ⟶ PSpace o m),
    g ≫ PSpace.str o m = g' ≫ PSpace.str o m →
    (∀ (A : Type) [CommRing A] (x : Sp A ⟶ Y) (v : Fin (m + 1) → A),
      SecCoord (GlobalTheory.ProjSpace.O1 o m) (GlobalTheory.ProjSpace.coord o m) (x ≫ g) v →
      SecCoord (GlobalTheory.ProjSpace.O1 o m) (GlobalTheory.ProjSpace.coord o m) (x ≫ g') v) → g = g' := by
  intro o _ Y m g g' hs H
  refine Scheme.hom_ext_of_forall _ _ fun t => ?_
  obtain ⟨W, hW, j, hj, ht, hc⟩ := RepUniq.exists_affine_secCoord (GlobalTheory.ProjSpace.O1_isLB o m)
    (GlobalTheory.ProjSpace.coord o m) g t
  obtain ⟨β, hβ⟩ := RepUniq.exists_spMap (A := Γ(Y, W)) ((hW.fromSpec ≫ g) ≫ PSpace.str o m)
  have hβ' : (hW.fromSpec ≫ g') ≫ PSpace.str o m = spMap β :=
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hs.symm)).trans ((Category.assoc _ _ _).symm.trans hβ)
  obtain ⟨_, e₁⟩ := eq_pt_of_secCoord β _ hβ _ hc
  obtain ⟨_, e₂⟩ := eq_pt_of_secCoord β _ hβ' _ (H _ hW.fromSpec _ hc)
  have e : hW.fromSpec ≫ g = hW.fromSpec ≫ g' := e₁.trans e₂.symm
  refine ⟨W, ht, ?_⟩
  rw [← RepUniq.isoSpec_hom_fromSpec hW, Category.assoc, Category.assoc, e]

end GlobalTheory.ZM.ProjExt
