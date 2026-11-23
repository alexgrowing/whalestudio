import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPelUnifTorsionIsoNontrivial
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CompactifiedModuliPartOne

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.Inhab

theorem exists_unif_nontrivial_torus : (∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : IsCMField E) (H : Host E) (t : SAB H (Sp (PowerSeries ℂ))) (P : PELUnif (Ideal.span {PowerSeries.X}) t), P.TorsionIso ∧ Nontrivial P.D.toPre.X) ∧ ∃ (D : Out.DegData (PowerSeries ℂ) (Ideal.span {PowerSeries.X})) (A : Out.PolAV (Spec (CommRingCat.of (FractionRing (PowerSeries ℂ))))) (G : Over (Spec (CommRingCat.of (PowerSeries ℂ)))) (_ : GrpObj G) (_ : IsCommMonObj G), IsSemiAbelian G ∧ Nontrivial D.toPre.X ∧ Nonempty (Out.Unif (Ideal.span {PowerSeries.X}) D A G) := by
  have h := exists_pelUnif_torsionIso_nontrivial GlobalTheory.partI_closed
  refine ⟨h, ?_⟩
  obtain ⟨E, _, _, _, H, t, P, -, hn⟩ := h
  exact ⟨P.D, P.A, t.G, inferInstance, inferInstance, t.semi, hn, ⟨P.U⟩⟩

end GlobalTheory.Inhab
