import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProjectorEigenDecomposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitting
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentBasisOfSplitTorsion
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GrNormPosOfBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeC
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_projector_eigen_decomposition : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (R : Type) [CommRing R] (κ : 𝓞 c.F →+* R) (g : ℕ) (ρ : 𝓞 E →+* Matrix (Fin g) (Fin g) R) (τ : E →+* ℂ), ∃ (D : ℕ) (P : Matrix (Fin g) (Fin g) R), D ≠ 0 ∧ P * P = (D : R) • P ∧ ∀ (K : Type) [CommRing K] (ψ : R →+* K) (φ : c.F →+* K), ψ.comp κ = φ.comp (algebraMap (𝓞 c.F) c.F) → ∀ cf : Fin g → K, ((∀ a, ((ρ a).map ψ).mulVec cf = φ (embK c τ a) • cf) ↔ (P.map ψ).mulVec cf = (D : K) • cf) := by
  first | exact @GlobalTheory.EigProjPoly.exists_scaled_eigProj | exact GlobalTheory.EigProjPoly.exists_scaled_eigProj | (intros; apply GlobalTheory.EigProjPoly.exists_scaled_eigProj <;> assumption)
