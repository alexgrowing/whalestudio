import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryTorusCompactQuotientFiniteVolume
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHasCls
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryTorus_compact_quotient_finite_volume : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r : ℕ) (P : PPol σ r), (∃ C : Set (Tor P (AF F)), IsCompact C ∧ ∀ t : Tor P (AF F), ∃ γ ∈ ratPts (star' P) (one₁ P), γ * t ∈ C) ∧ ∀ dt : Measure (Tor P (AF F)), dt.IsHaarMeasure → torVol P dt ≠ ⊤ := by
  first | exact @GlobalTheory.TorCompact.torus_compact_finiteVol | exact GlobalTheory.TorCompact.torus_compact_finiteVol | (intros; apply GlobalTheory.TorCompact.torus_compact_finiteVol <;> assumption)
