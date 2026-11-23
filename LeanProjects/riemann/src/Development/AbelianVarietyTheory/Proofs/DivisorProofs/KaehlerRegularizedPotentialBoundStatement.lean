import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KaehlerRegularizedPotentialBound
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open AlgebraicGeometry CategoryTheory MeasureTheory Set GlobalTheory.ShFam GlobalTheory.ChernReg GlobalTheory.CxPts GlobalTheory.TrueGeo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ShFam.Pad GlobalTheory.Toroidal GlobalTheory.ProjVar Formalism.L2.Pj Formalism.L2.Geo GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kaehler_regularized_potential_bound : KernelSt → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (σ : k →+* ℂ) (d : ℕ) [SmoothOfRelativeDimension d p], CompactSpace (CxPts p σ) → ∀ (a θ : ChartForm p σ d) (E : ChartMap p σ d) (ψ g : CxPts p σ → ℝ) (B : Set (CxPts p σ)), IsKaehlerForm (AnRead.all p σ d) a → IsExph a E → (∀ y, y ∉ B → ψ y = g y) → (∀ c : AlgChart p σ d, MeasureTheory.volume (c.e '' (B ∩ c.e.source)) = 0) → ∀ A K δ : ℝ, IsRegConst a θ (rho a E g) A K δ → ∃ δ' : ℝ, IsRegConst a θ (rho a E ψ) A K δ' := by
  first | exact @GlobalTheory.RegNullSet.transfer | exact GlobalTheory.RegNullSet.transfer | (intros; apply GlobalTheory.RegNullSet.transfer <;> assumption)
