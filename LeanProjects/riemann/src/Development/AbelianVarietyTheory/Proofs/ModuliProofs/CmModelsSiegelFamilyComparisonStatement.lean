import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModelsSiegelFamilyComparison
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Statements.HeckeInFamilies.GenericMemChart
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_models_siegel_family_comparison : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N : ℕ) (T : Top Xo n N), ToroidalLevelCompatibility (H := H) (D := D) → ∀ p : ℕ, p.Prime → p ≠ n → n.Prime → (∃ e, N = n ^ e) → ∃ Ag : SiegelFamily (Module.finrank ℚ E / 2 * (D.p + D.q)) p N, ∀ (W : ValuationSubring ℂ) (l₀ : Level H) (B : BaseModel T l₀) (l l₁ : Level H) (c : Coeff l) (c₁ : Coeff l₁) (Y : Model (Xo l) c (c.V W).subtype) (Y₁ : Model (Xo l₁) c₁ (c₁.V W).subtype) (b : c.V W →+* c₁.V W) (z : ZP p N →+* c₁.V W) (π : Y₁.X ⟶ Y.X), (p : ℂ) ∈ W.nonunits → IsPrimeToPart l₀ l p → n.Coprime l.M → IsIncl b → (∀ x, (((z x : c₁.V W) : c₁.F) : ℂ) = (x : ℂ)) → l₁.M = l.M → l₁.Mb = l.Mb → l₁.A = Nat.lcm l.A N → c₁.F = c.F ⊔ IntermediateField.adjoin ℚ {zeta N} → Raises B Y → Raises B Y₁ → IsTransition Y Y₁ b π → SiegelCompare Y Y₁ b π Ag z := by
  first | exact @GlobalTheory.SiegelComparison.siegelCompare | exact GlobalTheory.SiegelComparison.siegelCompare | (intros; apply GlobalTheory.SiegelComparison.siegelCompare <;> assumption)
