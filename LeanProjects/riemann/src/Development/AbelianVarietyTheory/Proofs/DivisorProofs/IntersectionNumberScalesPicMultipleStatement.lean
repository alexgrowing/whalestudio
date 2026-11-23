import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberScalesPicMultiple
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.GenericFiniteMaps
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (toMod)
open GlobalTheory.VB
open GlobalTheory.IndefiniteRowSideFullHecke.GenericFiniteMaps
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersection_number_scales_pic_multiple : ∀ (k : Type) [Field k] (T : Scheme.{0}) [Algebra k Γ(T, ⊤)], IsProjSurface k T → ∀ (L M : LB T) (hL : L.IsLB) (hM : M.IsLB) (n : ℕ), GlobalTheory.CechPic.cls M hM = n • GlobalTheory.CechPic.cls L hL → GlobalTheory.interNum k (structureModule T) ![M, M] = (n : ℤ) ^ 2 * GlobalTheory.interNum k (structureModule T) ![L, L] := by
  first | exact @GlobalTheory.Selfsq.selfInter_of_cls_eq_nsmul | exact GlobalTheory.Selfsq.selfInter_of_cls_eq_nsmul | (intros; apply GlobalTheory.Selfsq.selfInter_of_cls_eq_nsmul <;> assumption)
