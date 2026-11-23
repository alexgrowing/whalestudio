import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FibreLatticeBaseChangeConj
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.ThreeLeLevel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_lattice_base_change_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X' : Scheme.{0}) (t : SAB H X) (t' : SAB H X') (f : X' ⟶ X) (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (R R' : RiemLat E g Λ) (z : Sp ℂ ⟶ X'), (Nonempty (SABMap t' t f) → (FibreLat t' z R ↔ FibreLat t (z ≫ f) R)) ∧ ((∀ x, R'.P x = star (R.P x)) → R'.Hm = R.Hm.map (starRingEnd ℂ) → (∀ a x, R'.B a x = star (R.B a (star x))) → FibreLat t' z R → FibreLat t' (spMap (starRingEnd ℂ) ≫ z) R') := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.FibreMove.fibreLat_move | exact GlobalTheory.CompanionTheory.Ar.Cusp.FibreMove.fibreLat_move | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.FibreMove.fibreLat_move <;> assumption)
