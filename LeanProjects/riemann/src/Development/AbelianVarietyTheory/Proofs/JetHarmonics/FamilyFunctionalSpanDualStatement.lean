import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FamilyFunctionalSpanDual
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Definitions.Jets.TauZero
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jN2_eq_const_mul_formal_degree_of_supG : Hyps → ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (R : (Fin (2 * P.r + P.k + 1) → ℤ) → Rep P.k P.r) (l : ∀ ν, (R ν).H → Wp) (l' : ∀ ν, (R ν).H → Wq) (dg : (Fin (2 * P.r + P.k + 1) → ℤ) → ℝ) (s : (Fin (2 * P.r + P.k + 1) → ℤ) → ℂ) (J : (Fin (2 * P.r + P.k + 1) → ℤ) → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (tau : (Fin (2 * P.r + P.k + 1) → ℤ) → Finset (Fin (2 * P.r + P.k + 1)) → ℂ), Num P.k P.r lam P.u b bv ga h q0 → Sup p lam q0 R l l' dg s J tau → ∃ c : ℝ, 0 < c ∧ ∀ ν, n1 ν ≤ q0 → (J ν = 0 ∧ TBB.jN2 p (J ν) = 0 ∧ ¬ (NzOn (R ν) (l ν) ∧ NzOn (R ν) (l' ν))) ∨ (J ν ≠ 0 ∧ NzOn (R ν) (l ν) ∧ NzOn (R ν) (l' ν) ∧ s ν ≠ 0 ∧ TBB.jN2 p (J ν) = ENNReal.ofReal (c * Formalism.QuantumDeterminants.fdegHC (fun a => lam a + (ν a : ℝ)))) := by
  first | exact @GlobalTheory.SuppliedNorm.sup_norm | exact GlobalTheory.SuppliedNorm.sup_norm | (intros; apply GlobalTheory.SuppliedNorm.sup_norm <;> assumption)
