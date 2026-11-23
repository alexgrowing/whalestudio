import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ModelInclusionLevelChange
import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.model_inclusion_level_change : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N : ℕ) (T : Top Xo n N), ToroidalLevelCompatibility (H := H) (D := D) → ∀ (l₀ l : Level H) (B : BaseModel T l₀) (c : Coeff l) (R : Type) [CommRing R] (ω : R →+* c.F) (bR : RZ H (n * l₀.M) 1 →+* R), 0 < n → l₀.Dvd l → IsDedFrac ω → IsInc (RZ H (n * l₀.M) 1).subtype (c.F.val.toRingHom.comp ω) bR → ∃ (C : Model (Xo l) c ω) (k : KA l₀ →+* c.F) (r : (Xo l).XF c ⟶ (Xo l₀).X) (ν : SABMap C.oF.t (Xo l₀).univ.t r), r ≫ (Xo l₀).s = pullback.snd _ _ ≫ spMap k ∧ IsInc (KA l₀).val.toRingHom c.F.val.toRingHom k ∧ LevComp C.oF (Xo l₀).univ r ν ∧ Nonempty ((ofModel C).Above B.C bR r ν) := by
  first | exact @GlobalTheory.RaiseModel.exists_model_above | exact GlobalTheory.RaiseModel.exists_model_above | (intros; apply GlobalTheory.RaiseModel.exists_model_above <;> assumption)
