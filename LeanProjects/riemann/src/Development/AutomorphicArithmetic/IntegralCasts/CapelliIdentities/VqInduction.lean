import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qk61.VQ :
    {p : ℕ} → [inst : Fact (Nat.Prime p)] → GlobalTheory.UPel.HT.Datum p → Type :=
    fun {p : ℕ} [Fact (Nat.Prime p)] (D : GlobalTheory.UPel.HT.Datum p) ↦ TensorProduct ℤ ℚ D.La

theorem UpperTheory.Reformulated.B.Qk61.vq_induction :
    ∀ {p : ℕ} [inst : Fact (Nat.Prime p)] {D : GlobalTheory.UPel.HT.Datum p}
      {P : TensorProduct ℚ (GlobalTheory.LKTrip.AfP p) (UpperTheory.Reformulated.B.Qk61.VQ D) → Prop},
      P (0 : TensorProduct ℚ (GlobalTheory.LKTrip.AfP p) (UpperTheory.Reformulated.B.Qk61.VQ D)) →
        (∀ (x y : TensorProduct ℚ (GlobalTheory.LKTrip.AfP p) (UpperTheory.Reformulated.B.Qk61.VQ D)), P x → P y → P (x + y)) →
          (∀ (a : GlobalTheory.LKTrip.AfP p) (t : ℚ) (x : D.La), P (a ⊗ₜ[ℚ] (t ⊗ₜ[ℤ] x))) →
            ∀ (v : TensorProduct ℚ (GlobalTheory.LKTrip.AfP p) (UpperTheory.Reformulated.B.Qk61.VQ D)), P v := by
  intro p _ D P h0 hadd htmul v
  induction v using TensorProduct.induction_on with
  | zero => exact h0
  | add x y hx hy => exact hadd x y hx hy
  | tmul a w =>
    induction w using TensorProduct.induction_on with
    | zero => rw [TensorProduct.tmul_zero]; exact h0
    | tmul t x => exact htmul a t x
    | add x y hx hy => rw [TensorProduct.tmul_add]; exact hadd _ _ hx hy
