import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeModelVacuumTranslateClassesIndependent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Gam0
open Matrix

noncomputable section

namespace GlobalTheory.Hk3.VacPhase

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem cT_mul' (σ : L →+* L) {a b c : ℕ} (A : Matrix (Fin a) (Fin b) L) (B : Matrix (Fin b) (Fin c) L) :
    Formalism.UG.cT σ (A * B) = Formalism.UG.cT σ B * Formalism.UG.cT σ A := by
  simp only [Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_mul]

theorem cT_one' (σ : L →+* L) {a : ℕ} : Formalism.UG.cT σ (1 : Matrix (Fin a) (Fin a) L) = 1 := by
  simp [Formalism.UG.cT, Matrix.map_one]

theorem cT_sub' (σ : L →+* L) {a b : ℕ} (A B : Matrix (Fin a) (Fin b) L) :
    Formalism.UG.cT σ (A - B) = Formalism.UG.cT σ A - Formalism.UG.cT σ B := by
  ext i j; simp [Formalism.UG.cT]

theorem cT_add' (σ : L →+* L) {a b : ℕ} (A B : Matrix (Fin a) (Fin b) L) :
    Formalism.UG.cT σ (A + B) = Formalism.UG.cT σ A + Formalism.UG.cT σ B := by
  ext i j; simp [Formalism.UG.cT]

theorem mul_int {a b c : ℕ} {A : Matrix (Fin a) (Fin b) L} {B : Matrix (Fin b) (Fin c) L}
    (hA : ∀ i j, A i j ∈ Formalism.UG.intL L) (hB : ∀ i j, B i j ∈ Formalism.UG.intL L) (i : Fin a) (j : Fin c) :
    (A * B) i j ∈ Formalism.UG.intL L := by
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hA i k) (hB k j)

theorem cT_int (σ : L →+* L) (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {a b : ℕ} {A : Matrix (Fin a) (Fin b) L}
    (hA : ∀ i j, A i j ∈ Formalism.UG.intL L) (i : Fin b) (j : Fin a) : Formalism.UG.cT σ A i j ∈ Formalism.UG.intL L := by
  have h := hA j i
  change Valued.v (σ (A j i)) ≤ 1
  rw [hσ]; exact h

theorem locH_sub_trace_mem : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (δ : L), (∀ x, Valued.v (σ x) = Valued.v x) → δ ∈ Formalism.UG.intL L →
  ∀ (n n' : ℕ) (JS a k : GL (Fin n) L) (JT : GL (Fin n') L) (E : Matrix (Fin n) (Fin n) L) (y : Matrix (Fin n') (Fin n) L),
  (∀ i j, (JS : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L) → (∀ i j, ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L) →
  (∀ i j, (JT : Matrix (Fin n') (Fin n') L) i j ∈ Formalism.UG.intL L) → GlobalTheory.Hk3.HoweG.SelfDual σ JS a →
  Formalism.UG.cT σ E * (JS : Matrix (Fin n) (Fin n) L) = -((JS : Matrix (Fin n) (Fin n) L) * E) →
  (∀ i j, (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * E) i j ∈ Formalism.UG.intL L) → (∀ i j, (E * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) →
  (k : Matrix (Fin n) (Fin n) L) = 1 + E → (∀ i j, ((k⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L) →
  (∀ i j, (y * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) →
  GlobalTheory.Hk3.locH σ δ JS JT y (y * (((k⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) - 1)) -
    δ * Matrix.trace (E * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Formalism.UG.cT σ y * (JT : Matrix (Fin n') (Fin n') L) * y) ∈ Formalism.UG.intL L := by
  intro L _ _ σ δ hσ hδ n n' JS a k JT E y hJ hP hT hSD hE hAiE hEA hk hKi hyA
  set J : Matrix (Fin n) (Fin n) L := (JS : Matrix (Fin n) (Fin n) L) with hJdef
  set P : Matrix (Fin n) (Fin n) L := ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hPdef
  set T : Matrix (Fin n') (Fin n') L := (JT : Matrix (Fin n') (Fin n') L) with hTdef
  set K : Matrix (Fin n) (Fin n) L := (k : Matrix (Fin n) (Fin n) L) with hKdef
  set Ki : Matrix (Fin n) (Fin n) L := ((k⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hKidef
  set A : Matrix (Fin n) (Fin n) L := (a : Matrix (Fin n) (Fin n) L) with hAdef
  set Ai : Matrix (Fin n) (Fin n) L := ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hAidef
  have hPJ : P * J = 1 := by rw [hPdef, hJdef]; exact JS.inv_mul
  have hJP : J * P = 1 := by rw [hPdef, hJdef]; exact JS.mul_inv
  have hKKi : K * Ki = 1 := by rw [hKdef, hKidef]; exact k.mul_inv
  have hAAi : A * Ai = 1 := by rw [hAdef, hAidef]; exact a.mul_inv
  set R : Matrix (Fin n) (Fin n) L := P * Formalism.UG.cT σ Ki * J with hRdef
  set Z : Matrix (Fin n) (Fin n) L := P * Formalism.UG.cT σ y * T * y with hZdef

  have h1 : GlobalTheory.Hk3.locH σ δ JS JT y (y * (Ki - 1)) = δ * Matrix.trace ((R - 1) * Z) := by
    unfold GlobalTheory.Hk3.locH
    have : ((y * (Ki - 1)).map σ)ᵀ = Formalism.UG.cT σ (Ki - 1) * Formalism.UG.cT σ y := cT_mul' σ y (Ki - 1)
    rw [← hPdef, ← hTdef, this, cT_sub', cT_one']
    congr 1
    rw [hRdef, hZdef]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc J P, hJP, Matrix.one_mul]
  have h2 : δ * Matrix.trace (E * P * Formalism.UG.cT σ y * T * y) = δ * Matrix.trace (E * Z) := by
    rw [hZdef]; simp only [Matrix.mul_assoc]

  have hR : R * (1 - E) = 1 := by
    have hcK : Formalism.UG.cT σ K * J = J * (1 - E) := by
      rw [hk, cT_add', cT_one', Matrix.add_mul, hE, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, sub_eq_add_neg]
    rw [hRdef, Matrix.mul_assoc, ← hcK, ← Matrix.mul_assoc, Matrix.mul_assoc P, ← cT_mul', hKKi, cT_one', Matrix.mul_one, hPJ]
  have hR' : (1 - E) * R = 1 := mul_eq_one_comm.mp hR
  have hRE : R - 1 - E = E * R * E := by
    have e1 : R - 1 = R * E := by
      have := hR; rw [Matrix.mul_sub, Matrix.mul_one] at this
      rw [← this]; abel
    have e2 : R - 1 = E * R := by
      have := hR'; rw [Matrix.sub_mul, Matrix.one_mul] at this
      rw [← this]; abel
    calc R - 1 - E = (R - 1) * E := by rw [Matrix.sub_mul, Matrix.one_mul, e1]
      _ = E * R * E := by rw [e2]
  have h3 : GlobalTheory.Hk3.locH σ δ JS JT y (y * (Ki - 1)) - δ * Matrix.trace (E * P * Formalism.UG.cT σ y * T * y) =
      δ * Matrix.trace (R * (E * Z * E)) := by
    rw [h1, h2, ← mul_sub, ← Matrix.trace_sub, ← Matrix.sub_mul, hRE]
    congr 1
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm E]
    simp only [Matrix.mul_assoc]
  rw [h3]

  have hRint : ∀ i j, R i j ∈ Formalism.UG.intL L :=
    mul_int (mul_int hP (cT_int σ hσ hKi)) hJ
  have hy' : Formalism.UG.cT σ y = Formalism.UG.cT σ Ai * Formalism.UG.cT σ (y * A) := by
    rw [← cT_mul', Matrix.mul_assoc, hAAi, Matrix.mul_one]
  have hW : E * Z * E = ((E * A) * (Ai * P * Formalism.UG.cT σ Ai) * Formalism.UG.cT σ (y * A)) * T * ((y * A) * (Ai * E)) := by
    rw [hZdef, hy']
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc A Ai, hAAi, Matrix.one_mul, ← Matrix.mul_assoc A Ai E, hAAi, Matrix.one_mul]
  have hWint : ∀ i j, (E * Z * E) i j ∈ Formalism.UG.intL L := by
    rw [hW]
    exact mul_int (mul_int (mul_int (mul_int hEA hSD.2) (cT_int σ hσ hyA)) hT) (mul_int hyA hAiE)
  refine Subring.mul_mem _ hδ ?_
  exact Subring.sum_mem _ fun i _ => mul_int hRint hWint i i

end GlobalTheory.Hk3.VacPhase

end
