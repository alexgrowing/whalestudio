import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HomToCharacterLineEqZero
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.OnePlusPowerAssembly
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hom_to_characterLine_eq_zero : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt), Dt.T1 l → Dt.T2 l → Dt.T3 l → ∀ (e : ℤ), -1 ≤ e → e < Dt.t → ∀ (A₁ : Ob k G) (j : (Fin A₁.m → k) →ₗ[k] (Fin M.T.m → k)) (p : (Fin A₁.m → k) →ₗ[k] (Fin 1 → k)), IsHom A₁ M.T j → Function.Injective j → IsHom A₁ (chr (M.ω ^ (-e))) p → p = 0 := by
  first | exact @GlobalTheory.Models.ModTh.hom_chr_eq_zero | exact GlobalTheory.Models.ModTh.hom_chr_eq_zero | (intros; apply GlobalTheory.Models.ModTh.hom_chr_eq_zero <;> assumption)
