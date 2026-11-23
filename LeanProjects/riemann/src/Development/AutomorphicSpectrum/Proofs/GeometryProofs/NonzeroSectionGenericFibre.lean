import Mathlib
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace
import Development.AutomorphicSpectrum.Statements.GeometryStatements.KeyBadSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LeWchartOne
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EqZeroOfSmulEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.KeyGen GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg

namespace GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.Gen

theorem exists_generic_mem_nonzeroLocus : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G] [Smooth G.hom] [GeometricallyConnected G.hom] (M : LB G.left), M.IsLB → ∀ t : SecMod G.hom M, t ≠ 0 → ∀ b : Sp R, b.asIdeal = ⊥ → ∃ y : G.left, G.hom y = b ∧ y ∈ Out.nonzeroLocus (M := M) t := by
  intro R _ _ _ G _ _ _ M hM t ht b hb
  haveI hI : IsIntegral (Sp R) := by unfold Sp; infer_instance
  haveI hN : IsLocallyNoetherian (Sp R) := by unfold Sp; infer_instance
  haveI hGI : GeometricallyIntegral G.hom :=
    GlobalTheory.geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres G.hom
  haveI hGR : GeometricallyReduced G.hom := inferInstance
  haveI hRed : AlgebraicGeometry.IsReduced G.left :=
    GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian G.hom
  have hgen : GeneralizingMap G.hom.base := Flat.generalizingMap G.hom
  have hne : ∃ y, y ∈ Out.nonzeroLocus (M := M) t := by
    by_contra hcon
    simp only [not_exists] at hcon
    apply ht
    apply SecMod.ext
    intro k
    rw [zero_f, ← basicOpen_eq_bot_iff, eq_bot_iff]
    intro y hy
    exact absurd (by unfold Out.nonzeroLocus; exact TopologicalSpace.Opens.mem_iSup.mpr ⟨k, hy⟩) (hcon y)
  obtain ⟨y, hy⟩ := hne
  have hle : b.asIdeal ≤ (G.hom.base y).asIdeal := by rw [hb]; exact bot_le
  have hsp : b ⤳ G.hom.base y := (PrimeSpectrum.le_iff_specializes _ _).mp hle
  obtain ⟨y', hy'sp, hy'eq⟩ := hgen hsp
  exact ⟨y', hy'eq, hy'sp.mem_open (Out.nonzeroLocus (M := M) t).isOpen hy⟩

end GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.Gen
