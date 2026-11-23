import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMinAt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelToroidalPolCharts
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PullPowGen

theorem exists_isGenerated_and_isAmpleLB : ∀ (o : Type) [CommRing o] [IsNoetherianRing o] (Z S : Scheme.{0}) (z : Z ⟶ Sp o) (π : S ⟶ Z) (OZ : LB Z) (W M : LB S) (a N : ℕ), IsProjOver z → OZ.IsLB → GlobalTheory.IsAmpleLB OZ → W.IsLB → M.IsLB → 1 ≤ a → 1 ≤ N → LBIso (lbPow W N) (lbPow (OZ.pull π) a) → (∃ k₀ : ℕ, ∀ k, k₀ ≤ k → GlobalTheory.IsAmpleLB (GlobalTheory.CechPic.tens (lbPow (OZ.pull π) k) M)) → ∃ N' : ℕ, 1 ≤ N' ∧ GlobalTheory.IsGenerated (lbPow W N') ∧ ∃ k : ℕ, GlobalTheory.IsAmpleLB (GlobalTheory.CechPic.tens (lbPow W (N' * k)) M) := by
  intro o _ _ Z S z π OZ W M a N _ hO hA hW hM ha hN H ⟨k₀, hk₀⟩
  obtain ⟨b, hb, hgen⟩ := hA.exists_isGenerated_pow
  have hP : (OZ.pull π).IsLB := LB.isLB_pull hO π
  have hcls : N • CechPic.cls W hW = a • CechPic.cls (OZ.pull π) hP := by
    have := (CechPic.cls_eq_iff (isLB_lbPow hW N) (isLB_lbPow hP a)).2 H
    rwa [CechPic.cls_lbPow hW, CechPic.cls_lbPow hP] at this
  refine ⟨N * b, Nat.mul_pos hN hb, ?_, k₀, ?_⟩
  · have hg := (hgen.pull π).pow a
    have hOb := isLB_lbPow hO b
    have hPb := LB.isLB_pull hOb π
    refine hg.of_lbIso (isLB_lbPow hW _) ((CechPic.cls_eq_iff (isLB_lbPow hW _) hg.isLB).1 ?_)
    have e : CechPic.cls ((lbPow OZ b).pull π) hPb = b • CechPic.cls (OZ.pull π) hP := by
      rw [CechPic.cls_pull hOb, CechPic.cls_pull hO, CechPic.cls_lbPow hO, map_nsmul]
    rw [CechPic.cls_lbPow hW, CechPic.cls_lbPow hPb, e, mul_nsmul, hcls, ← mul_nsmul, ← mul_nsmul, mul_comm]
  · have hamp := hk₀ (a * (b * k₀)) (Nat.le_mul_of_pos_left _ ha |>.trans' (Nat.le_mul_of_pos_left _ hb))
    have hT := CechPic.isLB_tens (isLB_lbPow hW (N * b * k₀)) hM
    refine hamp.of_lbIso hT ((CechPic.cls_eq_iff hT hamp.isLB).1 ?_)
    rw [CechPic.cls_tens (isLB_lbPow hW _) hM, CechPic.cls_tens (isLB_lbPow hP _) hM, CechPic.cls_lbPow hW,
      CechPic.cls_lbPow hP, Nat.mul_assoc, mul_nsmul, hcls, ← mul_nsmul]

end GlobalTheory.PullPowGen
