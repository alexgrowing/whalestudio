import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNefSectionsAsymptotic
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsShiftSectionBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFujitaOne
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Imports
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AmpleSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.NefRR
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartLatQCech
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PQuotPartGraded
import Development.WeilBound.CoreStatements.HodgeTatePoints.A12

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel Filter Topology

namespace GlobalTheory.CompanionTheory.GenericFibre

theorem isMultiHomogIdeal_map_rat {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) :
    IsMultiHomogIdeal (P.map (MvPolynomial.map (Int.castRingHom ℚ))) := by
  obtain ⟨S, hS, rfl⟩ := hP
  refine ⟨MvPolynomial.map (Int.castRingHom ℚ) '' S, ?_, ?_⟩
  · rintro _ ⟨f, hf, rfl⟩
    obtain ⟨a, ha⟩ := hS f hf
    exact ⟨a, fun m hm k => ha m (MvPolynomial.support_map_subset _ _ hm) k⟩
  · exact Ideal.map_span _ _

theorem finiteDimensional_chartLatQ :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
      (y : (Σ k, ι k) → Ω) (D : ℕ) (b : K → ℤ),
      IsArithVar (mCoordIdeal y) (D + 1) → FiniteDimensional ℚ (chartLatQ y b 1) := by
  intro K _ ι _ Ω _ _ y D b hV
  classical
  letI : LinearOrder K := LinearOrder.lift' (Fintype.equivFin K) (Fintype.equivFin K).injective
  letI : ∀ k, LinearOrder (ι k) := fun k =>
    LinearOrder.lift' (Fintype.equivFin (ι k)) (Fintype.equivFin (ι k)).injective
  obtain ⟨e⟩ := ChartLatQCech.proof K ι Ω y (D + 1) b hV
  have hQ := isMultiHomogIdeal_map_rat hV.2.1.2.1
  have hG := QuotPartGraded.proof ℚ K ι _ hQ
  have hS := PositivityTheory.HtPt.Ktw.a11 ℚ K ι _
    (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.quotPart ℚ (Ideal.map (MvPolynomial.map (Int.castRingHom ℚ)) (mCoordIdeal y)))
    inferInstance inferInstance hG
  haveI := hS.1 b 0
  exact Module.Finite.equiv e.symm

end GlobalTheory.CompanionTheory.GenericFibre
