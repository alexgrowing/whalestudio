import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitriangularInductionTransvection
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitriangular_induction_on_transvections : ∀ (n : ℕ) (P : GL (Fin n) ℂ → Prop), P 1 → (∀ A B, P A → P B → P (A * B)) → (∀ (i j : Fin n), i < j → ∀ (s : ℂ) (B : GL (Fin n) ℂ), B.val = transvection i j s → P B) → ∀ U : GL (Fin n) ℂ, U.val.BlockTriangular id → (∀ i, U.val i i = 1) → P U := by
  first | exact @GlobalTheory.unitriangular_induction_transvection | exact GlobalTheory.unitriangular_induction_transvection | (intros; apply GlobalTheory.unitriangular_induction_transvection <;> assumption)
