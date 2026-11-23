import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleIsoNhdOfStalkBaseChange
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lineBundleIso_nhd_of_stalk_baseChange : ∀ {S X : Scheme.{0}} [IsLocallyNoetherian S] (h : X ⟶ S) [QuasiCompact h] [QuasiSeparated h] (x : S) (A B : LB X), A.IsLB → B.IsLB → LBIso (A.pull (pullback.fst h (S.fromSpecStalk x))) (B.pull (pullback.fst h (S.fromSpecStalk x))) → ∃ W : S.Opens, x ∈ W ∧ LBIso (A.pull (h ⁻¹ᵁ W).ι) (B.pull (h ⁻¹ᵁ W).ι) := by
  first | exact @GlobalTheory.StalkLBIso.exists_lbIso_nhd | exact GlobalTheory.StalkLBIso.exists_lbIso_nhd | (intros; apply GlobalTheory.StalkLBIso.exists_lbIso_nhd <;> assumption)
