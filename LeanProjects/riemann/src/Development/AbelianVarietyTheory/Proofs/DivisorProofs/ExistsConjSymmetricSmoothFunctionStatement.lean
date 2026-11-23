import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjSymmetricSmoothFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualRef
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conj_symmetric_smooth_function : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (e : ℕ) (M : Man e) (I : ManIs M Y) (f : M.Fun), M.Smooth f → ∃ f' : M.Fun, M.Smooth f' ∧ ∀ a a' x x', (I.pt a' x').1 = spMap (starRingEnd ℂ) ≫ (I.pt a x).1 → f' a' x' = f a x := by
  first | exact @GlobalTheory.Mean4O.ConjSmooth.exists_smooth_conj | exact GlobalTheory.Mean4O.ConjSmooth.exists_smooth_conj | (intros; apply GlobalTheory.Mean4O.ConjSmooth.exists_smooth_conj <;> assumption)
