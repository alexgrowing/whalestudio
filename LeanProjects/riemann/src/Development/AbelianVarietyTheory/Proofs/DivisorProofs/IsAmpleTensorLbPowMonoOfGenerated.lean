import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EvenDefect
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelToroidalPolCharts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecCmp
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.AmpleTwistLarger

theorem isAmpleLB_tens_lbPow_succ {S : Scheme.{0}} {L M : LB S} {N m : ℕ} (hL : L.IsLB) (hM : M.IsLB)
    (hG : GlobalTheory.IsGenerated (lbPow L N)) (hA : GlobalTheory.IsAmpleLB (GlobalTheory.CechPic.tens (lbPow L (N * m)) M)) :
    GlobalTheory.IsAmpleLB (GlobalTheory.CechPic.tens (lbPow L (N * (m + 1))) M) := by
  have h₁ := GlobalTheory.isLB_lbPow hL (N * (m + 1))
  have h₂ := GlobalTheory.isLB_lbPow hL (N * m)
  have h₃ := GlobalTheory.isLB_lbPow hL N
  have hT := GlobalTheory.CechPic.isLB_tens h₁ hM
  have hS := GlobalTheory.CechPic.isLB_tens h₂ hM
  have hq := LB.isLB_div hT hS
  refine hA.tensor_isGenerated hG hT ((GlobalTheory.CechPic.cls_eq_zero_iff (LB.isLB_div hq h₃)).1 ?_)
  rw [GlobalTheory.CechPic.cls_div hq h₃, GlobalTheory.CechPic.cls_div hT hS, GlobalTheory.CechPic.cls_tens h₁ hM,
    GlobalTheory.CechPic.cls_tens h₂ hM, GlobalTheory.CechPic.cls_lbPow hL, GlobalTheory.CechPic.cls_lbPow hL, GlobalTheory.CechPic.cls_lbPow hL,
    Nat.mul_succ, add_smul]
  abel

theorem isAmpleLB_tens_lbPow_of_le : ∀ (S : Scheme.{0}) (L M : LB S) (N k : ℕ), L.IsLB → M.IsLB → GlobalTheory.IsGenerated (lbPow L N) → GlobalTheory.IsAmpleLB (GlobalTheory.CechPic.tens (lbPow L (N * k)) M) → ∀ k', k ≤ k' → GlobalTheory.IsAmpleLB (GlobalTheory.CechPic.tens (lbPow L (N * k')) M) := by
  intro S L M N k hL hM hG hA k' hk
  induction k', hk using Nat.le_induction with
  | base => exact hA
  | succ m _ ih => exact isAmpleLB_tens_lbPow_succ hL hM hG ih

end GlobalTheory.AmpleTwistLarger
