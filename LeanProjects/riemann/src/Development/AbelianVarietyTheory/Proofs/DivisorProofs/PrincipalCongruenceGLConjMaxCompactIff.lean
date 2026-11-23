import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Definitions.Divisors.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulMat
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

noncomputable section

namespace GlobalTheory.CongConj

variable {E : Type} [Field E] [NumberField E] {w : Pl E} {m : ℕ}

theorem v_le_one_of_mem_KGL {c : GLw m w} (hc : c ∈ GlobalTheory.LFun.KGL w m) (i j : Fin m) :
    Valued.v (c.val i j) ≤ 1 := by
  obtain ⟨a, rfl⟩ := hc
  exact (a.val i j).2

theorem v_mul_left_le {A B : Matrix (Fin m) (Fin m) (w.adicCompletion E)} {γ : WithZero (Multiplicative ℤ)}
    (hA : ∀ i j, Valued.v (A i j) ≤ 1) (hB : ∀ i j, Valued.v (B i j) ≤ γ) (i j : Fin m) :
    Valued.v ((A * B) i j) ≤ γ := by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun l _ => ?_
  rw [map_mul]
  exact mul_le_of_le_one_of_le (hA i l) (hB l j)

theorem v_mul_right_le {A B : Matrix (Fin m) (Fin m) (w.adicCompletion E)} {γ : WithZero (Multiplicative ℤ)}
    (hA : ∀ i j, Valued.v (A i j) ≤ γ) (hB : ∀ i j, Valued.v (B i j) ≤ 1) (i j : Fin m) :
    Valued.v ((A * B) i j) ≤ γ := by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun l _ => ?_
  rw [map_mul]
  exact mul_le_of_le_of_le_one (hA i l) (hB l j)

theorem conj_imp (k : ℕ) {c N : GLw m w} (hc : c ∈ GlobalTheory.LFun.KGL w m)
    (hN : N ∈ GlobalTheory.LFun.KGL w m ∧ ∀ i j, Valued.v (N.val i j - (1 : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j) ≤
      WithZero.exp (-(k : ℤ))) :
    c⁻¹ * N * c ∈ GlobalTheory.LFun.KGL w m ∧ ∀ i j, Valued.v ((c⁻¹ * N * c).val i j -
      (1 : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ)) := by
  refine ⟨mul_mem (mul_mem (inv_mem hc) hN.1) hc, fun i j => ?_⟩
  have hid : (c⁻¹ * N * c).val - 1 = (c⁻¹).val * (N.val - 1) * c.val := by
    have h1 : (c⁻¹).val * c.val = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    simp only [Units.val_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h1]
  have := v_mul_right_le (v_mul_left_le (B := N.val - 1) (v_le_one_of_mem_KGL (inv_mem hc)) (fun a b => by
    rw [Matrix.sub_apply]; exact hN.2 a b)) (v_le_one_of_mem_KGL hc) i j
  rw [← hid, Matrix.sub_apply] at this
  exact this

end GlobalTheory.CongConj

theorem GlobalTheory.congConj_iff : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (m k : ℕ) (c N : GLw m w), c ∈ GlobalTheory.LFun.KGL w m → ((c⁻¹ * N * c ∈ GlobalTheory.LFun.KGL w m ∧ ∀ i j, Valued.v ((c⁻¹ * N * c).val i j - (1 : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))) ↔ (N ∈ GlobalTheory.LFun.KGL w m ∧ ∀ i j, Valued.v (N.val i j - (1 : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ)))) := by
  intro E _ _ w m k c N hc
  constructor
  · intro h
    have h2 := GlobalTheory.CongConj.conj_imp k (inv_mem hc) h
    simpa [mul_assoc] using h2
  · exact GlobalTheory.CongConj.conj_imp k hc
