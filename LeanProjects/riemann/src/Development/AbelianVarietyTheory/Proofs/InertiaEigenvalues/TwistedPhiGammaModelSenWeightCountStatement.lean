import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedPhiGammaModelSenWeightCount
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.OnePlusPowerAssembly
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedPhiGammaModel_sen_weight_count : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt), Dt.T1 l → Dt.T2 l → Dt.T3 l → ∀ N : Lats k n M.T.m, M.Model M.T N → (∀ i, M.Nstd i ≤ N i) → ∀ i, (∀ a : ℕ, a ≤ Dt.sg l i + 1 → sen ((F.D M.T).γ i) (N i) (a : k) = 0) ∧ (Dt.ty i = LType.G → ∑ j ∈ Finset.range (Dt.w i).toNat, sen ((F.D M.T).γ i) (N i) ((-Dt.w i + j : ℤ) : k) = Dt.d i) ∧ (Dt.ty i = LType.Bd → Dt.d i + ∑ a ∈ Finset.range ((Dt.wst i).toNat + 1), sen ((F.D M.T).γ i) (N i) (a : k) = r) := by
  first | exact @GlobalTheory.ModelCount.count | exact GlobalTheory.ModelCount.count | (intros; apply GlobalTheory.ModelCount.count <;> assumption)
