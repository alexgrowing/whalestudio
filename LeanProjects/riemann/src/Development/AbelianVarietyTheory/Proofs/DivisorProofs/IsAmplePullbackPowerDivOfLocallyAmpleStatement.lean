import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmplePullbackPowerDivOfLocallyAmple
import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOfQuasiAffine
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAmple_pullbackPower_div_of_locally_ample : ∀ {W S : Scheme.{0}} [CompactSpace W] [QuasiSeparatedSpace W] (f : W ⟶ S) (A : LB S), IsAmpleLB A → ∀ (N M : LB W) (hN : N.IsLB) (hM : M.IsLB), GlobalTheory.CechPic.cls M hM = -GlobalTheory.CechPic.cls N hN → (∀ z : S, ∃ V : S.Opens, z ∈ V ∧ IsAffineOpen V ∧ IsAmpleLB (M.pull (f ⁻¹ᵁ V).ι)) → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → IsAmpleLB (LB.div (lbPow (A.pull f) n) N) := by
  first | exact @GlobalTheory.AmpleTwistLB.ample_pow_div | exact GlobalTheory.AmpleTwistLB.ample_pow_div | (intros; apply GlobalTheory.AmpleTwistLB.ample_pow_div <;> assumption)
