import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolUnifCompareIsogeny
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HodgeIPIffHodgeFormConj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hol_unif_compare_isogeny : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] (L : LB G.left) (z : Spec (CommRingCat.of ℂ) ⟶ X) (A A' : Over (Sp ℂ)) [GrpObj A] [GrpObj A'] (φ : A.left ⟶ G.left) (φ' : A'.left ⟶ G.left) (g g' : ℕ) (u : HolUnif A (L.pull φ) g) (u' : HolUnif A' (L.pull φ') g') (Hm : Matrix (Fin g) (Fin g) ℂ) (Hm' : Matrix (Fin g') (Fin g') ℂ) (χ : u.Λ → ℂ) (χ' : u'.Λ → ℂ), L.IsLB → IsAbelianScheme A → IsGrpPullback A G z φ → IsGrpPullback A' G z φ' → (∀ v, IsTangent v → ∃! w, u.IsDiff w v) → (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) → u.IsAH Hm χ → u'.IsAH Hm' χ' → ∀ (x y : epsR ℂ ⟶ A) (x' y' : epsR ℂ ⟶ A') (a b : Fin g → ℂ) (a' b' : Fin g' → ℂ), IsTangent x → IsTangent y → x'.left ≫ φ' = x.left ≫ φ → y'.left ≫ φ' = y.left ≫ φ → u.IsDiff a x → u.IsDiff b y → u'.IsDiff a' x' → u'.IsDiff b' y' → hermForm Hm' a' b' = hermForm Hm a b := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HodgeUniq.hermForm_eq_of_pullbacks | exact GlobalTheory.CompanionTheory.Ar.HodgeUniq.hermForm_eq_of_pullbacks | (intros; apply GlobalTheory.CompanionTheory.Ar.HodgeUniq.hermForm_eq_of_pullbacks <;> assumption)
