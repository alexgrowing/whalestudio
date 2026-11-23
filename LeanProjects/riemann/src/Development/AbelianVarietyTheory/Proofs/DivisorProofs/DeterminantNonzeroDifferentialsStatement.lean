import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantNonzeroDifferentials
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
  IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum polydisc defCoord cWt)

attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.determinant_nonzero_differentials : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (X : Obj F 𝔠 (Sp ℂ)) (L : LB X.A.left)
    (u : HolUnif X.A L (Module.finrank ℚ F)) (δ : X.DetGen) (v : Fin (Module.finrank ℚ F) → X.Lie)
    (W : Matrix (Fin (Module.finrank ℚ F)) (Fin (Module.finrank ℚ F)) ℂ),
    (∀ j, u.IsDiff (W j) (v j).hom) → W.det ≠ 0 → δ.1 v ≠ 0 := by
  first | exact @GlobalTheory.LatJet.detGen_apply_ne_zero_of_isDiff | exact GlobalTheory.LatJet.detGen_apply_ne_zero_of_isDiff | (intros; apply GlobalTheory.LatJet.detGen_apply_ne_zero_of_isDiff <;> assumption)
