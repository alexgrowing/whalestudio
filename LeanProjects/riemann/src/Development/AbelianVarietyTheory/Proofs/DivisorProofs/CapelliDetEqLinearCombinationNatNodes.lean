import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QdetPolyMapMonic
open NumberField GlobalTheory.CuspRep

noncomputable section

open Polynomial Finset

namespace GlobalTheory.CuspRep

theorem eval_eq_sum_lagrange_nodes (b : ℕ) (u : ℂ) (f : ℂ[X]) (hf : f.degree < ((b + 1 : ℕ) : WithBot ℕ)) :
    f.eval u = ∑ j : Fin (b + 1),
      (Lagrange.basis univ (fun j : Fin (b + 1) => ((j : ℕ) : ℂ)) j).eval u * f.eval ((j : ℕ) : ℂ) := by
  have hinj : Set.InjOn (fun j : Fin (b + 1) => ((j : ℕ) : ℂ)) (univ : Finset (Fin (b + 1))) := by
    intro x _ y _ h
    exact Fin.ext (by simpa using h)
  have e := Lagrange.eq_interpolate (s := univ) hinj (f := f) (by simpa using hf)
  conv_lhs => rw [e]
  rw [Lagrange.interpolate_apply, eval_finsetSum]
  refine sum_congr rfl fun j _ => ?_
  rw [eval_mul, eval_C, mul_comm]

theorem cap_eq_sum_nodes (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (b : ℕ) (τ : E →+* ℂ) (u : ℂ) :
    ∃ w : Fin (b + 1) → ℂ, cap (a := b) τ u = ∑ j : Fin (b + 1), w j • cap (a := b) τ ((j : ℕ) : ℂ) := by
  obtain ⟨c, -, hc⟩ := GlobalTheory.qdet_polyMap_monic (Module.End ℂ (Sm E b)) b (Eop τ)
  have hcap : ∀ v : ℂ, cap (a := b) τ v =
      ∑ i ∈ range (b + 1), ((X + C (((b : ℂ) - 1) / 2)) ^ i).eval v • c i := by
    intro v
    rw [cap, hc]
    simp only [eval_pow, eval_add, eval_X, eval_C]
  refine ⟨fun j => (Lagrange.basis univ (fun j : Fin (b + 1) => ((j : ℕ) : ℂ)) j).eval u, ?_⟩
  simp_rw [hcap, smul_sum, smul_smul]
  rw [sum_comm]
  refine sum_congr rfl fun i hi => ?_
  rw [← sum_smul, ← eval_eq_sum_lagrange_nodes]
  have hi' : i < b + 1 := mem_range.1 hi
  rw [degree_pow, degree_X_add_C]
  simp only [nsmul_eq_mul, mul_one]
  exact_mod_cast hi'

end GlobalTheory.CuspRep
