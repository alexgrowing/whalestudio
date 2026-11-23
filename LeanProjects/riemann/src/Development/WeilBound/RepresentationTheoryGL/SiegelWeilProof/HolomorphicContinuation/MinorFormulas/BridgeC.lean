import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.BridgeB

noncomputable section

open Matrix Filter Topology

namespace PositivityTheory.Rg.Sw.SP

open PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z

variable {n : ℕ}

def gD (s : ℂ) (x : MC n) (k l : Fin n) (kk : Bool × Fin n × Fin n) : ℂ :=
  if kk.1 then (-(Complex.I * s) • (Yp s x * Matrix.of (eU k l) * Yp s x)) kk.2.1 kk.2.2
  else ((Complex.I * s) • (Ym s x * Matrix.of (eU k l) * Ym s x)) kk.2.1 kk.2.2

theorem hasDerivAt_vals (s : ℂ) (x : MC n) (hx : x ∈ OmS s) (k l : Fin n) (kk : Bool × Fin n × Fin n) :
    HasDerivAt (fun t : ℂ => vals s (x + t • eU k l) kk) (gD s x k l kk) 0 := by
  obtain ⟨b, a, d⟩ := kk
  cases b
  · simpa [vals, gD] using hYm n s x (eU k l) hx.1 a d
  · simpa [vals, gD] using hYp n s x (eU k l) hx.2.1 a d

theorem hasDerivAt_evQ (s z : ℂ) (x : MC n) (hx : x ∈ OmS s) (k l : Fin n) (Q : Fm n) :
    HasDerivAt (fun t : ℂ => evQ s z Q (x + t • eU k l))
      (∑ kk, evQ s z (MvPolynomial.pderiv kk Q) x * gD s x k l kk) 0 := by
  have h := hasDerivAt_eval (fun t : ℂ => vals s (x + t • eU k l)) (gD s x k l) (hasDerivAt_vals s x hx k l)
    (MvPolynomial.map (Polynomial.evalRingHom z) Q)
  simp only [zero_smul, add_zero] at h
  refine h.congr_deriv ?_
  refine Finset.sum_congr rfl fun kk _ => ?_
  rw [MvPolynomial.pderiv_map]
  rfl

theorem sum_bool_fin (F : Bool × Fin n × Fin n → ℂ) :
    ∑ kk, F kk = ∑ a : Fin n, ∑ d : Fin n, F (false, a, d) + ∑ a : Fin n, ∑ d : Fin n, F (true, a, d) := by
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [Fintype.sum_prod_type]
  ring

theorem line_fQ (s : ℂ) (hs : s = 1 ∨ s = -1) (z : ℂ) (m : ℕ) (Q : Fm n) (x : MC n) (hx : x ∈ OmS s) (k l : Fin n) :
    HasDerivAt (fun t : ℂ => fQ s z m Q (x + t • eU k l)) (fQ s z m (opD s m k l Q) x) 0 := by
  have h1 := hCls n s hs z m x (eU k l) hx
  have h2 := hasDerivAt_evQ s z x hx k l Q
  have h3 := h1.mul h2
  refine h3.congr_deriv ?_
  simp only [fQ, opD, LinearMap.add_apply, opH_eq, evQ_add, evQ_multPart, evQ_derPart, trace_eU, sum_bool_fin, gD,
    Bool.false_eq_true, if_false, if_true, Matrix.smul_apply, sandwich_eU, smul_eq_mul, cB, alB, vals,
    Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X, zero_smul, add_zero]
  simp only [Finset.mul_sum, Finset.sum_add_distrib, mul_add]
  ring_nf
  congr 1
  · congr 1
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun d _ => ?_
    ring
  · refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun d _ => ?_
    ring

end PositivityTheory.Rg.Sw.SP
