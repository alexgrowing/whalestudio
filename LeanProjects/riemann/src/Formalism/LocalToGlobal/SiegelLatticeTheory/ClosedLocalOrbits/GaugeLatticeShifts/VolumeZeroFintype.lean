import Mathlib

noncomputable section

open MeasureTheory
open scoped ComplexConjugate

namespace Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames

def PF (ι : Type*) : Subalgebra ℂ ((ι → ℝ) → ℂ) :=
  (MvPolynomial.aeval (R := ℂ) (fun i (y : ι → ℝ) => (y i : ℂ))).range

theorem PF_eval {ι : Type*} (p : MvPolynomial ι ℂ) (y : ι → ℝ) :
    (MvPolynomial.aeval (R := ℂ) (fun i (y : ι → ℝ) => (y i : ℂ)) p : (ι → ℝ) → ℂ) y =
      MvPolynomial.eval (fun i => (y i : ℂ)) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [MvPolynomial.aeval_C]
  | add p q hp hq => simp only [map_add, Pi.add_apply, hp, hq]
  | mul_X p i hp => simp only [map_mul, Pi.mul_apply, hp, MvPolynomial.aeval_X, MvPolynomial.eval_X]

theorem PF_mem_iff {ι : Type*} {f : (ι → ℝ) → ℂ} :
    f ∈ PF ι ↔ ∃ p : MvPolynomial ι ℂ, ∀ y, f y = MvPolynomial.eval (fun i => (y i : ℂ)) p := by
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨p, fun y => PF_eval p y⟩
  · rintro ⟨p, hp⟩
    exact ⟨p, funext fun y => (PF_eval p y).trans (hp y).symm⟩

theorem PF_const {ι : Type*} (a : ℂ) : (fun _ : ι → ℝ => a) ∈ PF ι :=
  PF_mem_iff.2 ⟨MvPolynomial.C a, fun y => by simp⟩

theorem PF_conj {ι : Type*} {f : (ι → ℝ) → ℂ} (hf : f ∈ PF ι) : (fun y => conj (f y)) ∈ PF ι := by
  obtain ⟨p, hp⟩ := PF_mem_iff.1 hf
  refine PF_mem_iff.2 ⟨MvPolynomial.map (starRingEnd ℂ) p, fun y => ?_⟩
  rw [hp, MvPolynomial.eval_map]
  show starRingEnd ℂ (MvPolynomial.eval₂ (RingHom.id ℂ) _ p) = _
  rw [MvPolynomial.eval₂_comp_left, RingHom.comp_id]
  congr 1
  funext i
  simp

end Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames
