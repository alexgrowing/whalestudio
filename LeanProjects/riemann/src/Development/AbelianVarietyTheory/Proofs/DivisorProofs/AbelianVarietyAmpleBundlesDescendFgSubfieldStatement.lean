import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyAmpleBundlesDescendFgSubfield
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianVariety_ampleBundles_descend_fg_subfield : ∀ (K : Type) [Field K] [CharZero K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (L M : LB A.left), L.IsLB → M.IsLB → RelAmple A L → RelAmple A M → LBIso (L.pull (GrpObj.inv : A ⟶ A).left) L → LBIso (M.pull (GrpObj.inv : A ⟶ A).left) M → ∃ (k₀ : IntermediateField ℚ K) (A₀ : Over (Sp k₀)) (_ : GrpObj A₀) (π : A.left ⟶ A₀.left) (L₀ M₀ : LB A₀.left), k₀.FG ∧ IsAbelianScheme A₀ ∧ IsGrpPullback A A₀ (spMap (algebraMap k₀ K)) π ∧ L₀.IsLB ∧ M₀.IsLB ∧ RelAmple A₀ L₀ ∧ RelAmple A₀ M₀ ∧ LBIso (L₀.pull (GrpObj.inv : A₀ ⟶ A₀).left) L₀ ∧ LBIso (M₀.pull (GrpObj.inv : A₀ ⟶ A₀).left) M₀ ∧ LBIso L (L₀.pull π) ∧ LBIso M (M₀.pull π) := by
  first | exact @GlobalTheory.AbFGSpread.spread_to_fg_subfield | exact GlobalTheory.AbFGSpread.spread_to_fg_subfield | (intros; apply GlobalTheory.AbFGSpread.spread_to_fg_subfield <;> assumption)
