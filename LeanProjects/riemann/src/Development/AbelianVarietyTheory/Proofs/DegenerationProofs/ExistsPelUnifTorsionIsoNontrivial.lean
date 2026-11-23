import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AdmissibleBasePowerSeries
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsPrimitiveRootArcRoot
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.OneAddZeta21PowSevenAddPowFourteenEqZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LinearUniformisationTriplesTorsionStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcWitnessModelPointStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.Inhab

theorem exists_pelUnif_torsionIso_nontrivial : PartI → ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : IsCMField E) (H : Host E) (t : SAB H (Sp (PowerSeries ℂ))) (P : PELUnif (Ideal.span {PowerSeries.X}) t), P.TorsionIso ∧ Nontrivial P.D.toPre.X := by
  intro h
  obtain ⟨E, i₁, i₂, i₃, H, D, l, Xo, c, W₀, Y, bF, j₁, j₂, a, χ, w, g, ty, Fu, -, -, -, -, -, -, hn, -⟩ :=
    GlobalTheory.T.arc_witness_model_point h
  haveI : CharZero (PowerSeries ℂ) := algebraRat.charZero _
  obtain ⟨P, hD, -, -, hP⟩ := GlobalTheory.T.linearUniformisation_triples_torsion E H (PowerSeries ℂ) _ (admissibleBase_powerSeries ℂ) w.t w.P.D w.P.A w.P.U w.P.bundle
  exact ⟨E, i₁, i₂, i₃, H, w.t, P, hP, hD ▸ hn⟩

end GlobalTheory.Inhab
