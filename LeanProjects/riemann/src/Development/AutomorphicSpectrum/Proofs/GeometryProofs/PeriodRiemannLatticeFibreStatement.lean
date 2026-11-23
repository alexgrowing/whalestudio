import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodRiemannLatticeFibre
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUniqueLeftBasisCoordsAdicCompletion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsOver
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.NineStatements GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.FamEx
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_riemann_lattice_fibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo σ ty) (i : Fin FU.n) (P : (FU.Di i).La →+ (Fin g → ℂ)), IsTypeFn H D.p D.q ty → IsPeriod (FU.Di i) ty P → (∃ R : RiemLat E g (FU.Di i).La, R.form = (FU.Di i).EF ∧ FibreLat Xo.univ.t (FU.u i P) R ∧ ∀ s : E →+* ℂ, Module.finrank ℂ (eigSp R.B (s.comp (algebraMap (𝓞 E) E))) = if s (H.rt : E) = H.rt0 then D.p else D.q) ∧ (∃ R : RiemLat E g (FU.Di i).La, R.form = -(FU.Di i).EF ∧ FibreLat Xo.univ.t (spMap (starRingEnd ℂ) ≫ FU.u i P) R ∧ ∀ s : E →+* ℂ, Module.finrank ℂ (eigSp R.B (s.comp (algebraMap (𝓞 E) E))) = if s (H.rt : E) = H.rt0 then D.q else D.p) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.period_lattice_fibre_and_conj | exact GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.period_lattice_fibre_and_conj | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.period_lattice_fibre_and_conj <;> assumption)
