import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisChangeTorsion
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitKOfIsAlgClosed
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_basis_change_torsion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X), X.IsSeparated → ∀ (p : ℕ) [Fact p.Prime] (x : Sp ↥(intO ℂ_[p]) ⟶ X) (g g' : ℕ) (e : Fin g → (Sp (DualNumber ↥(intO ℂ_[p])) ⟶ t.G.left)) (e' : Fin g' → (Sp (DualNumber ↥(intO ℂ_[p])) ⟶ t.G.left)), IsTanBasis t x e → IsTanBasis t x e' → ∀ (c : TorsChar t x (p ^ 2)) (h : Fin g → ↥(intO ℂ_[p])) (h' : Fin g' → ↥(intO ℂ_[p])), DlogIs t p 2 c e h → DlogIs t p 2 c e' h' → ∀ (a : Fin g → ℂ_[p]) (a' : Fin g' → ℂ_[p]) (w : Sp (DualNumber ℂ_[p]) ⟶ t.G.left), IsCombAtG t (spMap (intO ℂ_[p]).subtype ≫ x) (fun i => spMap (dualMap (intO ℂ_[p]).subtype) ≫ e i) a w → IsCombAtG t (spMap (intO ℂ_[p]).subtype ≫ x) (fun i => spMap (dualMap (intO ℂ_[p]).subtype) ≫ e' i) a' w → w ∈ latHT t p (spMap (intO ℂ_[p]).subtype ≫ x) → ‖∑ i, (h i : ℂ_[p]) * a i - ∑ i, (h' i : ℂ_[p]) * a' i‖ < 1 := by
  first | exact @GlobalTheory.HtGen.DlogClose.dlog_sub_norm_lt_one | exact GlobalTheory.HtGen.DlogClose.dlog_sub_norm_lt_one | (intros; apply GlobalTheory.HtGen.DlogClose.dlog_sub_norm_lt_one <;> assumption)
