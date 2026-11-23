import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisLatticePresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitting
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_basis_lattice_presentation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (T : Scheme.{0}) (t : SAB H T) (R : Type) [CommRing R] (x : Sp R ⟶ T) (kind : ℕ → Bool) (sc : ℕ → ℝ) (g M : ℕ) (e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)) (h : Fin M → Fin g → R), GlobalTheory.LineNorm.IsTanBasis t x e → LatPres t x kind (fun _ => 0) e h → ∀ (m : ℕ) (d : Fin m → R), (∃ n : ℕ, n ≠ 0 ∧ (n : R) ∈ Ideal.span (Set.range d)) → (∀ (p : ℕ) [Fact p.Prime] (φ : R →+* ↥(intO ℂ_[p])), ‖fun k => ((φ (d k) : ↥(intO ℂ_[p])) : ℂ_[p])‖ = (p : ℝ) ^ (-sc p)) → ∃ (M' : ℕ) (h' : Fin M' → Fin g → R), LatPres t x kind sc e h' := by
  first | exact @GlobalTheory.ArLieBase.latPres_scale | exact GlobalTheory.ArLieBase.latPres_scale | (intros; apply GlobalTheory.ArLieBase.latPres_scale <;> assumption)
