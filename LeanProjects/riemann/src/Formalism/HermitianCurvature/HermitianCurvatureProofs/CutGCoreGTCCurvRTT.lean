import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCCurvCut

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

open Formalism.FourierDecayAlt.P.MAx3.G

section PolyTools

variable {R : Type} [Ring R] [Algebra ℂ R]

theorem curv_polyIn_congr {f g : ℂ → R} {d : ℕ} (h : PolyIn f d) (e : ∀ s, g s = f s) : PolyIn g d := by
  obtain ⟨a, ha⟩ := h
  exact ⟨a, fun s => by rw [e, ha]⟩

theorem curv_polyIn_csmul {f : ℂ → R} {d : ℕ} (c : ℂ) (hf : PolyIn f d) : PolyIn (fun s => c • f s) d := by
  obtain ⟨a, ha⟩ := hf
  exact ⟨fun k => c • a k, fun s => by dsimp only; rw [ha, Finset.smul_sum]; simp only [smul_comm c]⟩

theorem curv_polyIn_sub {f g : ℂ → R} {d : ℕ} (hf : PolyIn f d) (hg : PolyIn g d) :
    PolyIn (fun s => f s - g s) d :=
  curv_polyIn_congr (polyIn_add hf (curv_polyIn_csmul (-1) hg)) fun s => by simp [sub_eq_add_neg]

theorem curv_polyIn_monomial (n : ℕ) (x : R) : PolyIn (fun s => s ^ n • x) n := by
  refine ⟨fun k => if k = n then x else 0, fun s => ?_⟩
  dsimp only
  rw [Finset.sum_eq_single n (fun b _ hb => by rw [if_neg hb, smul_zero])
    (fun h => absurd (Finset.mem_range.2 (Nat.lt_succ_self n)) h), if_pos rfl]

end PolyTools

theorem curv_top_zero {E : Type*} [AddCommGroup E] [Module ℂ E] (n : ℕ) (c : E) (a : ℕ → E)
    (h : ∀ u : ℂ, u ^ (n + 1) • c = ∑ i ∈ Finset.range (n + 1), u ^ i • a i) : c = 0 := by
  rw [← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro φ
  set p : Polynomial ℂ := Polynomial.C (φ c) * Polynomial.X ^ (n + 1) -
    ∑ i ∈ Finset.range (n + 1), Polynomial.C (φ (a i)) * Polynomial.X ^ i with hpdef
  have hp : p = 0 := by
    apply Polynomial.funext
    intro u
    have hu := congrArg φ (h u)
    simp only [map_smul, map_sum, smul_eq_mul] at hu
    simp only [hpdef, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_finsetSum, Polynomial.eval_zero]
    rw [mul_comm (φ c), hu, sub_eq_zero]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hc := congrArg (fun q => Polynomial.coeff q (n + 1)) hp
  simp only [hpdef, Polynomial.coeff_sub, Polynomial.coeff_C_mul_X_pow, Polynomial.finsetSum_coeff,
    Polynomial.coeff_zero] at hc
  rw [Finset.sum_eq_zero (fun i hi => by
    rw [if_neg (by have := Finset.mem_range.1 hi; omega)]), sub_zero] at hc
  exact hc

theorem curvature_radial_torus_holds : GTCCurvRTT := by
  intro A _ _ n f g Θ hn hrtt hF hg v
  set T := g v with hT
  set F : ℂ → A := fun u => f u - u ^ (n + 1) • (1 : A) - u ^ n • Θ with hFdef
  have hn' : n - 1 + 1 = n := Nat.sub_add_cancel hn
  have hG : PolyIn (fun u => F u * T - T * F u) (n - 1) :=
    curv_polyIn_sub (polyIn_mul_const hF T) (polyIn_const_mul T hF)
  have hSt : PolyIn (fun u => g u * f v - u ^ n • (T * Θ) - T * F u + v • (u ^ n • (Θ * T - T * Θ)) -
      u • (F u * T - T * F u) + v • (F u * T - T * F u)) n := by
    refine polyIn_add (curv_polyIn_sub (polyIn_add (curv_polyIn_sub (curv_polyIn_sub (polyIn_mul_const hg (f v))
      (curv_polyIn_monomial n (T * Θ))) (polyIn_mono (polyIn_const_mul T hF) (by omega)))
      (curv_polyIn_csmul v (curv_polyIn_monomial n (Θ * T - T * Θ)))) ?_) ?_
    · have := polyIn_smul_var hG
      rw [hn'] at this
      exact this
    · exact polyIn_mono (curv_polyIn_csmul v hG) (by omega)
  obtain ⟨s, hs⟩ := hSt
  have key : ∀ u : ℂ, u ^ (n + 1) • (Θ * T - T * Θ + T) = ∑ i ∈ Finset.range (n + 1), u ^ i • s i := by
    intro u
    rw [← hs u]
    have hfu : f u = F u + u ^ (n + 1) • (1 : A) + u ^ n • Θ := by simp only [hFdef]; abel
    have h := hrtt u v
    rw [← hT, hfu] at h
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one] at h
    linear_combination (norm := module) h
  have h0 := curv_top_zero n _ s key
  exact eq_neg_of_add_eq_zero_left h0

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
