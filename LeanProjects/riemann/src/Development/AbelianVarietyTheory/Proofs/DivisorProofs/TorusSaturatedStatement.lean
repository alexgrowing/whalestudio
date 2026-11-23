import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusLieAlgebraCoordinateLinearEquivStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusClosedImmersionGenericFromSpecialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusLieAlgebraRetractionExistsStatement

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs

namespace GlobalTheory.TorusSat

open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps (torus lieMap lieAdd LieCongr IsLieLinear lieCoord IsSaturatedTorus TorusSaturated)

theorem lieCongr_of_retraction {R : Type} [CommRing R] {T G : Over (Spec (CommRingCat.of R))}
    [GrpObj T] [GrpObj G] (u : T ⟶ G) [IsMonHom u] (ρ : LieG G → LieG T) (hρ : IsLieLinear ρ)
    (hρu : ∀ x, ρ (lieMap u x) = x) (I : Ideal R) (x y : LieG T)
    (h : LieCongr G I (lieMap u x) (lieMap u y)) : LieCongr T I x y := by
  obtain ⟨a, ha, z, hz⟩ := h
  refine ⟨a, ha, ρ z, ?_⟩
  have := congrArg ρ hz
  rw [hρu, hρ.1, hρu, hρ.2] at this
  exact this

theorem torusSaturated (h : GlobalTheory.CovTop.Hypotheses2) : TorusSaturated := by
  intro R _ _ _ K _ _ _ G _ hG r uK huK hci
  obtain ⟨u, ⟨hu, hu'⟩, huniq⟩ :=
    GlobalTheory.Published.SemiAbelianHomExtension.dvr (K := K) h.p22 (G := torus R r) (H := G)
      (GlobalTheory.Diag.isSemiAbelian _ _) hG uK
  refine ⟨u, hu, hu', fun u' h1 h2 => huniq u' ⟨h1, h2⟩, ?_⟩
  have hsp := GlobalTheory.T.torus_closed_immersion_special_of_generic h R K G hG r u hu (hu' ▸ hci)
  obtain ⟨ρ, hρ, hρu⟩ := GlobalTheory.T.torus_lie_algebra_retraction_exists R G hG.smooth r u hsp
  exact ⟨hsp, fun x y hxy => lieCongr_of_retraction u ρ hρ hρu _ x y hxy, GlobalTheory.T.torus_lie_algebra_coordinate_linear_equiv R r, ρ, hρ, hρu⟩

theorem main : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.TorusSaturated := torusSaturated

end GlobalTheory.TorusSat
