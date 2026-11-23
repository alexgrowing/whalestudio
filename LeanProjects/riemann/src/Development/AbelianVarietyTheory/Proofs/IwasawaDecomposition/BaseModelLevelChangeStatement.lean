import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseModelLevelChange
import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_model_level_change : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N : ℕ) (T : Top Xo n N) (l₀ l : Level H) (B : BaseModel T l₀) (c : Coeff l) (R O' : Type) [CommRing R] [CommRing O'] (ω : R →+* c.F) (β' : O' →+* c.F) (bR : RZ H (n * l₀.M) 1 →+* R) (C : Model (Xo l) c ω) (Y' : Model (Xo l) c β') (b' : R →+* O') (k : KA l₀ →+* c.F) (r : (Xo l).XF c ⟶ (Xo l₀).X) (ν : SABMap C.oF.t (Xo l₀).univ.t r), r ≫ (Xo l₀).s = pullback.snd _ _ ≫ spMap k → IsInc (KA l₀).val.toRingHom c.F.val.toRingHom k → LevComp C.oF (Xo l₀).univ r ν → (ofModel C).Above B.C bR r ν → IsDedFrac ω → IsDedFrac β' → β'.comp b' = ω → Raises B Y' → Dominates C Y' b' := by
  first | exact @GlobalTheory.Models.Domination.dominates_of_above | exact GlobalTheory.Models.Domination.dominates_of_above | (intros; apply GlobalTheory.Models.Domination.dominates_of_above <;> assumption)
