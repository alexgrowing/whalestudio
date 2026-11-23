import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMoveRight
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemParahoricOfTrivialReduction
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedK1BlockDecomposition
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

namespace GlobalTheory.QCong

theorem conj_extE_cong : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) {n : ℕ} (c j D : ℕ) (h : Sp E (n + c) ≃ₗ[E] Sp E (n + c)) (κ : GLint E n P), κ ∈ GlobalTheory.TopStep.prinCong n P D → j + 1 ≤ D → (∀ x ∈ stdAt E (n + c) P, h⁻¹ x ∈ stdAt E (n + c) P ∧ ((qOf P : E) ^ j) • h x ∈ stdAt E (n + c) P) → ∀ x ∈ stdAt E (n + c) P, (qOf P : E)⁻¹ • ((h⁻¹ * GlobalTheory.CongLevel.extE c κ.1 * h) x - x) ∈ stdAt E (n + c) P := by
  intro E _ _ _ P n c j D h κ hκ hjD hh x hx
  obtain ⟨m, rfl⟩ : ∃ m, D = j + 1 + m := ⟨D - (j + 1), by omega⟩
  have hq : ((qOf P : ℕ) : E) ≠ 0 := GlobalTheory.TopStep.qOf_ne_zero
  have hu := (hh x hx).2
  have hw : GlobalTheory.CongLevel.resX c (((qOf P : E) ^ j) • h x) ∈ stdAt E n P :=
    GlobalTheory.TopStep.mem_stdAt.2 fun i => GlobalTheory.TopStep.mem_stdAt.1 hu (Fin.castAdd c i)
  have hw' := (GlobalTheory.TopStep.mem_prinCong.1 hκ) _ hw
  have key : (qOf P : E)⁻¹ • (GlobalTheory.CongLevel.extE c κ.1 (h x) - h x) = ((qOf P : E) ^ m) • Loc.inX E n c
      ((((qOf P : E) ^ (j + 1 + m))⁻¹) • (κ.1 (GlobalTheory.CongLevel.resX c (((qOf P : E) ^ j) • h x)) - GlobalTheory.CongLevel.resX c (((qOf P : E) ^ j) • h x))) := by
    rw [GlobalTheory.CongLevel.extE_apply, add_sub_cancel_left, map_smul (GlobalTheory.CongLevel.resX c), map_smul κ.1, ← smul_sub, smul_smul,
      ← map_smul, ← map_smul, smul_smul]
    congr 2
    field_simp
    ring
  have e1 : (h⁻¹ * GlobalTheory.CongLevel.extE c κ.1 * h) x - x = h⁻¹ (GlobalTheory.CongLevel.extE c κ.1 (h x) - h x) := by
    rw [map_sub]
    congr 1
    exact (LinearEquiv.symm_apply_apply h x).symm
  rw [e1, ← map_smul, key]
  refine (hh _ ?_).1
  refine GlobalTheory.TopStep.mem_stdAt.2 fun l => ?_
  rw [Pi.smul_apply, smul_eq_mul, GlobalTheory.CongLevel.inX_apply]
  split_ifs with hl
  · exact (GlobalTheory.TopStep.intAt_pow (GlobalTheory.TopStep.intAt_nat _) m).mul (GlobalTheory.TopStep.mem_stdAt.1 hw' _)
  · rw [mul_zero]; exact GlobalTheory.TopStep.intAt_zero

end GlobalTheory.QCong
