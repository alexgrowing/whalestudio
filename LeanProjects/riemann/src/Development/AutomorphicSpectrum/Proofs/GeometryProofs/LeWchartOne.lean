import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.KeyBadSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg

theorem le_wchart_one {X : Scheme.{0}} (L : LB X) (i : L.ι) :
    L.U i ≤ LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => i) :=
  fun _ hy => Set.mem_iInter.2 fun _ => hy

def SameSec {X : Scheme.{0}} {L : LB X} (s : Out.H0 L 1) (th : L.Sec) : Prop :=
  ∀ i, th.f i = (X.presheaf.map (homOfLE (le_wchart_one L i)).op).hom (s.f fun _ => i)

def NonVan {S Y : Scheme.{0}} (p : Y ⟶ S) {M : LB Y} (s : M.Sec) : Prop :=
  ∀ b : S, ∃ y : Y, p y = b ∧ y ∈ Out.nonzeroLocus s

end GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg
