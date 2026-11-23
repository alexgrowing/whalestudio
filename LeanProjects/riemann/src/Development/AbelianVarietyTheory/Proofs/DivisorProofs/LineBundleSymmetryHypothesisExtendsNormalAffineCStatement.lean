import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSymmetryHypothesisExtendsNormalAffineC
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnivBasis
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleSymmetryHypothesis_extends_normal_affineChart : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (U : M.Z.Opens), IsAffineOpen U → (U : Set M.Z).Nonempty → GlobalTheory.IsNormalScheme M.Z → ∀ (R₀ : Type) [CommRing R₀] (P : PolAV (Sp R₀)) (P' : PolAV (Sp (M.ringOn U))) (P₀ : PolAV (Sp Ω)) (f : R₀ →+* Ω) (a : P₀.A.left ⟶ P.A.left) (a' : P₀.A.left ⟶ P'.A.left), IsGrpPullback P₀.A P.A (spMap f) a → IsGrpPullback P₀.A P'.A (spMap (M.ringOn U).val.toRingHom) a' → LBIso P₀.L (P.L.pull a) → LBIso P₀.L (P'.L.pull a') → HypS P.A P.L → HypS P'.A P'.L := by
  first | exact @GlobalTheory.Poinc.hypS_of_generic_ringOn | exact GlobalTheory.Poinc.hypS_of_generic_ringOn | (intros; apply GlobalTheory.Poinc.hypS_of_generic_ringOn <;> assumption)
