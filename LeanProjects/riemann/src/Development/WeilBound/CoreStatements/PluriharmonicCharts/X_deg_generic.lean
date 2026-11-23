import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.AutomorphicSpectrum.Proofs.MetricProofs.DegreeGenericOfDegree
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ExistsLinearIndependentOfGenerates
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ExistsUnique
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyBridgeFull
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

theorem PositivityTheory.Xgp.t_deg_generic : Inputs → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (I : IFamily ℚ ι), IsFieldIntersection I → ∀ (D : ℕ) (P : Ideal (MRing ι)) (L : Fin D → HermLine ι), IsArithVar P (D + 1) → (∀ j, IsSmoothHerm (L j)) → ptsIntegral P (pot L) (fun _ => 1) = (I (P.map (MvPolynomial.map (Int.castRingHom ℚ))) D fun j => (L j).a : ℤ) := by
  intro hI K _ ι _ I hF D P L hP hL
  classical
  obtain ⟨I₀, -, hu⟩ := GroundTheory.Heights₂.Heights.Targets.ExistsUnique.full ℚ ι
  have hQ := GroundTheory.Heights₂.Heights.HilbertSamuel.isProjVarF_map_of_isArithVar hP
  have h1 := hu I hF _ D (fun j => (L j).a) hQ
  have h2 := hu _ (GroundTheory.Heights₂.Heights.NumbersDVR.IntNumIsFieldIntersection.full ℚ K ι) _ D (fun j => (L j).a) hQ
  rw [h1, ← h2]
  exact GlobalTheory.CompanionTheory.Ar.Giv.degreeGeneric_of_degree hI.degree K ι P D L hP hL
