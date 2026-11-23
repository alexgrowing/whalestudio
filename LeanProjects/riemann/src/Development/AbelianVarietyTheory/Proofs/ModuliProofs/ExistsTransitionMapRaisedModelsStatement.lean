import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTransitionMapRaisedModels
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
theorem _root_.GlobalTheory.T.exists_transition_map_raised_models : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N : ℕ) (T : Top Xo n N), ToroidalLevelCompatibility (H := H) (D := D) → ∀ (l₀ l₀' : Level H) (B : BaseModel T l₀) (B' : BaseModel T l₀') (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model (Xo l) c β) (l₂ : Level H) (c₂ : Coeff l₂) (O₂ : Type) [CommRing O₂] (β₂ : O₂ →+* c₂.F) (Y₂ : Model (Xo l₂) c₂ β₂) (b : O →+* O₂), 0 < n → (∃ e, N ∣ n ^ e) → l₀.Dvd l₀' → l₀.Dvd l → l₀'.Dvd l₂ → l.Dvd l₂ → c.F ≤ c₂.F → IsDedFrac β → IsDedFrac β₂ → IsInc (c.F.val.toRingHom.comp β) (c₂.F.val.toRingHom.comp β₂) b → Raises B Y → Raises B' Y₂ → ∃ π : Y₂.X ⟶ Y.X, IsTransition Y Y₂ b π := by
  first | exact @GlobalTheory.RaisedTransition.exists_isTransition | exact GlobalTheory.RaisedTransition.exists_isTransition | (intros; apply GlobalTheory.RaisedTransition.exists_isTransition <;> assumption)
