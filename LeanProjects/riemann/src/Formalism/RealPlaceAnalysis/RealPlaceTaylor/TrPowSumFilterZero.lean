import Formalism.RealPlaceAnalysis.StatementB

open Finset

noncomputable section

namespace Formalism.REAL

def TrPow_m {n : ℕ} (l : Fin n → ℂ) : ℕ → Fin n → ℂ
  | 0 => fun _ => 1
  | k + 1 => fun a => l a * TrPow_m l k a - ∑ b ∈ univ.filter (fun b => a < b), TrPow_m l k b

lemma TrPow_m_zero {n : ℕ} (l : Fin n → ℂ) (a : Fin n) : TrPow_m l 0 a = 1 := rfl

lemma TrPow_m_succ {n : ℕ} (l : Fin n → ℂ) (k : ℕ) (a : Fin n) :
    TrPow_m l (k + 1) a = l a * TrPow_m l k a - ∑ b ∈ univ.filter (fun b => a < b), TrPow_m l k b :=
  rfl

lemma TrPow_diag (h : HWDiag) {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (ν : Fin n → ℂ) (v : V) (hE : GlRel E)
    (hv : IsHW E ν v) : ∀ (k : ℕ) (a : Fin n), epow E k a a v = TrPow_m (lsh ν) k a • v := by
  intro k
  induction k with
  | zero => intro a; simp [epow, TrPow_m_zero]
  | succ k ih =>
    intro a
    rw [h V n E ν v hE hv k a, TrPow_m_succ, ih a]
    simp only [ih]
    rw [← Finset.sum_smul, sub_smul, mul_smul]

end Formalism.REAL
