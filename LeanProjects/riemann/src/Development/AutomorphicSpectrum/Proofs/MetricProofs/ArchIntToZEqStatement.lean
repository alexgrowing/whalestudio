import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ArchIntToZEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ArFormExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CodimOneIntegralSubschemeDim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleProductOfEach
import Development.AbelianVarietyTheory.Definitions.Divisors.GenericPointAsIdeal
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.SheetUnsheet
import Development.AutomorphicSpectrum.PublishedTheorems.Divisibility₂.PairingExists
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ GlobalTheory.CompanionTheory.Ar.BGS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archInt_toZ_eq : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (D : ℕ), IsArithVar p D → ∀ (N M : HermLB p) (hN : ∀ τ, (wZ N t τ).IsCInf) (hM : ∀ τ, (wZ M t τ).IsCInf) (e : ℕ) (r : M.B.ι → X.functionFieldˣ) (hr : IsRatSec M.B r), ((toZ N t hN).ArchIntegrable (toZ M t hM) e hr ↔ N.ArchIntegrable M e hr) ∧ (N.ArchIntegrable M e hr → (toZ N t hN).archInt (toZ M t hM) e hr = N.archInt M e hr) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BaseZ.archInt_toZ | exact GlobalTheory.CompanionTheory.Ar.BaseZ.archInt_toZ | (intros; apply GlobalTheory.CompanionTheory.Ar.BaseZ.archInt_toZ <;> assumption)
