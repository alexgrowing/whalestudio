import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.BridgeA

noncomputable section

open Matrix Filter Topology

namespace PositivityTheory.Rg.Sw.SP

open PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z

variable {n : ℕ}

theorem evQ_mul (s z : ℂ) (P Q : Fm n) (B : MC n) : evQ s z (P * Q) B = evQ s z P B * evQ s z Q B := by
  simp [evQ]

theorem evQ_add (s z : ℂ) (P Q : Fm n) (B : MC n) : evQ s z (P + Q) B = evQ s z P B + evQ s z Q B := by
  simp [evQ]

theorem evQ_sum (s z : ℂ) {ι : Type} (t : Finset ι) (P : ι → Fm n) (B : MC n) :
    evQ s z (∑ i ∈ t, P i) B = ∑ i ∈ t, evQ s z (P i) B := by
  simp [evQ, map_sum]

theorem evQ_CC (s z a : ℂ) (B : MC n) : evQ s z (MvPolynomial.C (Polynomial.C a)) B = a := by
  simp [evQ]

theorem evQ_C (s z : ℂ) (p : Polynomial ℂ) (B : MC n) : evQ s z (MvPolynomial.C p) B = p.eval z := by
  simp [evQ]

theorem evQ_yv (s z : ℂ) (b : Bool) (i j : Fin n) (B : MC n) : evQ s z (yv b i j) B = vals s B (b, i, j) := by
  simp [evQ, yv]

theorem evQ_multPart (s z : ℂ) (m : ℕ) (b : Bool) (k l : Fin n) (Q : Fm n) (B : MC n) :
    evQ s z (multPart s m b k l Q) B = -(cB s b) * ((alB m b).eval z * vals s B (b, l, k) * evQ s z Q B) := by
  rw [multPart_apply, evQ_mul, evQ_CC, evQ_mul, evQ_mul, evQ_C, evQ_yv]

theorem evQ_derPart (s z : ℂ) (b : Bool) (k l : Fin n) (Q : Fm n) (B : MC n) :
    evQ s z (derPart s b k l Q) B = ∑ a : Fin n, ∑ d : Fin n,
      -(cB s b) * (vals s B (b, a, k) * vals s B (b, l, d) * evQ s z (MvPolynomial.pderiv (b, a, d) Q) B) := by
  rw [derPart_apply, evQ_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [evQ_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [evQ_mul, evQ_CC, evQ_mul, evQ_mul, evQ_yv, evQ_yv]

theorem trace_eU (Y : Matrix (Fin n) (Fin n) ℂ) (k l : Fin n) : (Y * Matrix.of (eU k l)).trace = Y l k := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply, eU]
  rw [Finset.sum_eq_single l]
  · rw [Finset.sum_eq_single k]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  · intro b _ hb
    refine Finset.sum_eq_zero fun j _ => ?_
    simp [hb]
  · simp

theorem sandwich_eU (Y : Matrix (Fin n) (Fin n) ℂ) (k l a d : Fin n) :
    (Y * Matrix.of (eU k l) * Y) a d = Y a k * Y l d := by
  simp only [Matrix.mul_apply, Matrix.of_apply, eU]
  rw [Finset.sum_eq_single l]
  · rw [Finset.sum_eq_single k]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  · intro b _ hb
    rw [Finset.sum_eq_zero]
    · simp
    intro j _
    simp [hb]
  · simp

end PositivityTheory.Rg.Sw.SP
