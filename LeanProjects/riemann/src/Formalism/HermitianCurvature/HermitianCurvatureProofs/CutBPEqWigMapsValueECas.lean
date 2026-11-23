import Formalism.HermitianCurvature.HermitianCurvatureProofs.LowKAllPos
import Formalism.HermitianCurvature.CapelliDeterminantAndBranching

open Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P.WigCas

open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Qr

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem cas_comm {A : Type*} [Ring A] {n : ℕ} {E : Fin n → Fin n → A} (hE : GlRel E) (c d : Fin n) :
    Cas E * E c d = E c d * Cas E := by
  have expand : Cas E * E c d - E c d * Cas E = ∑ a, ∑ b, (E a b * ((if a = c then E b d else 0) -
      (if d = b then E c a else 0)) + ((if b = c then E a d else 0) - (if d = a then E c b else 0)) * E b a) := by
    simp only [Cas, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    rw [← hE b a c d, ← hE a b c d]
    noncomm_ring
  have hT1 : ∑ a, ∑ b, E a b * (if a = c then E b d else 0) = ∑ b, E c b * E b d := by
    rw [Finset.sum_eq_single c (fun a _ ha => by simp [ha]) (by simp)]
    simp
  have hT4 : ∑ a, ∑ b, (if d = a then E c b else 0) * E b a = ∑ b, E c b * E b d := by
    rw [Finset.sum_eq_single d (fun a _ ha => by simp [Ne.symm ha]) (by simp)]
    simp
  have hT2 : ∑ a, ∑ b, E a b * (if d = b then E c a else 0) = ∑ a, E a d * E c a := by
    simp [mul_ite]
  have hT3 : ∑ a, ∑ b, (if b = c then E a d else 0) * E b a = ∑ a, E a d * E c a := by
    simp [ite_mul]
  rw [← sub_eq_zero, expand]
  simp only [mul_sub, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hT1, hT2, hT3, hT4]
  abel

def casV {n : ℕ} (ν : Fin n → ℂ) : ℂ := ∑ a, ν a ^ 2 + ∑ a, ∑ b, if a < b then ν a - ν b else 0

end Formalism.FourierDecayAlt.P.WigCas

end
