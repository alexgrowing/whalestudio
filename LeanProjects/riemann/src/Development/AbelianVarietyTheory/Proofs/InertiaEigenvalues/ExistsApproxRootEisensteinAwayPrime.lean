import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BezoutEisensteinDerivativePrimePowStatement

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem eval_derivative_scaleRoots_mul {R : Type*} [CommRing R] (P : Polynomial R) (s x : R) :
    (Polynomial.derivative (P.scaleRoots s)).eval (s * x) =
      s ^ (P.natDegree - 1) * (Polynomial.derivative P).eval x := by
  have h1 : (Polynomial.derivative (P.scaleRoots s)).natDegree < P.natDegree - 1 + 1 := by
    have := Polynomial.natDegree_derivative_le (P.scaleRoots s)
    rw [Polynomial.natDegree_scaleRoots] at this
    omega
  have h2 : (Polynomial.derivative P).natDegree < P.natDegree - 1 + 1 := by
    have := Polynomial.natDegree_derivative_le P
    omega
  rw [Polynomial.eval_eq_sum_range' h1, Polynomial.eval_eq_sum_range' h2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ P.natDegree - 1 := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  rw [Polynomial.coeff_derivative, Polynomial.coeff_derivative, Polynomial.coeff_scaleRoots]
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hi'
  have h3 : P.natDegree - (i + 1) = k := by omega
  rw [h3, hk]
  ring

theorem exists_approx_root_scaleRoots {R : Type*} [CommRing R] (P : Polynomial R) (hP : 0 < P.natDegree)
    (t x b : R) (c : ℕ) (hb : P.eval x ∣ b * (Polynomial.derivative P).eval x - t ^ c) (n : ℕ) :
    ∃ (m : ℕ) (q : R), P.eval x ∣ q - t ^ m * x ∧ P.eval x ^ (n + 1) ∣ (P.scaleRoots (t ^ m)).eval q := by
  induction n with
  | zero => exact ⟨0, x, by simp, by simp⟩
  | succ n ih =>
    obtain ⟨m, q, ⟨z, hz⟩, ⟨w, hw⟩⟩ := ih
    obtain ⟨e, he⟩ : ∃ e, P.natDegree = e + 1 := ⟨P.natDegree - 1, by omega⟩
    obtain ⟨v, hv⟩ := hb
    set E := P.eval x with hE
    set s := t ^ m with hs
    set r := t ^ c * s ^ e with hr
    have hsr : t ^ (m + (c + m * e)) = s * r := by rw [hr, hs]; ring
    set h := -(b * (P.scaleRoots s).eval q) with hh
    refine ⟨m + (c + m * e), r * q + h, ?_, ?_⟩
    · rw [hsr]
      refine ⟨r * z - b * E ^ n * w, ?_⟩
      rw [hh, hw]
      linear_combination r * hz
    · rw [hsr]
      obtain ⟨k, hk⟩ := Polynomial.binomExpansion (P.scaleRoots (s * r)) (r * q) h
      have h0 : (P.scaleRoots (s * r)).eval (r * q) = r ^ (e + 1) * (P.scaleRoots s).eval q := by
        rw [Polynomial.scaleRoots_mul, Polynomial.scaleRoots_eval_mul, Polynomial.natDegree_scaleRoots, he]
      have h1 := eval_derivative_scaleRoots_mul P (s * r) x
      rw [he, Nat.add_sub_cancel] at h1
      obtain ⟨y, hy⟩ := Polynomial.sub_dvd_eval_sub (r * q) (s * r * x)
        (Polynomial.derivative (P.scaleRoots (s * r)))
      have h2 : (Polynomial.derivative (P.scaleRoots (s * r))).eval (r * q) =
          (s * r) ^ e * (Polynomial.derivative P).eval x + E * (r * z * y) := by
        rw [← h1]
        linear_combination hy + r * y * hz
      rw [hk, h0, h2, hh, hw]
      refine ⟨-((s * r) ^ e * v * w) - b * w * (r * z * y) + k * b ^ 2 * w ^ 2 * E ^ n, ?_⟩
      have h3 : r ^ (e + 1) = (s * r) ^ e * t ^ c := by
        rw [pow_succ, mul_pow]; nth_rewrite 2 [hr]; ring
      rw [h3]
      linear_combination (-((s * r) ^ e * E ^ (n + 1) * w)) * hv

theorem BK.exists_approx_root : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (n : ℕ),
    ∃ (m : ℕ) (q : bk.S), bk.E ∣ q - (l : bk.S) ^ m * X ∧
      bk.E ^ n ∣ Polynomial.eval₂ PowerSeries.C q (bk.Ep.scaleRoots ((l : Wq l bk.a) ^ m)) := by
  intro l _ K bk n
  obtain ⟨c, a, b, hab⟩ := GlobalTheory.T.bezout_eisenstein_derivative_prime_pow l K bk
  have hcoe : ∀ p : Polynomial (Wq l bk.a),
      (p.map (PowerSeries.C : Wq l bk.a →+* bk.S)).eval (X : bk.S) = (p : bk.S) := fun p => by
    rw [Polynomial.eval_map, Polynomial.eval₂_C_X_eq_coe]
  have hdeg : (bk.Ep.map (PowerSeries.C : Wq l bk.a →+* bk.S)).natDegree = bk.Ep.natDegree :=
    bk.monic.natDegree_map _
  have hb : (bk.Ep.map (PowerSeries.C : Wq l bk.a →+* bk.S)).eval (X : bk.S) ∣
      (b : bk.S) * (Polynomial.derivative (bk.Ep.map (PowerSeries.C : Wq l bk.a →+* bk.S))).eval X -
        (l : bk.S) ^ c := by
    rw [Polynomial.derivative_map, hcoe, hcoe]
    have h := congrArg (fun p : Polynomial (Wq l bk.a) => (p : bk.S)) hab
    beta_reduce at h
    rw [Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_mul, Polynomial.coe_C, map_pow, map_natCast] at h
    exact ⟨-(a : bk.S), by linear_combination h⟩
  obtain ⟨m, q, h1, h2⟩ := exists_approx_root_scaleRoots _ (hdeg ▸ bk.deg_pos) (l : bk.S) X b c hb n
  rw [hcoe] at h1 h2
  refine ⟨m, q, h1, (pow_dvd_pow _ n.le_succ).trans ?_⟩
  rw [← Polynomial.eval_map, Polynomial.map_scaleRoots _ _ _ (by rw [bk.monic.leadingCoeff, map_one]; exact one_ne_zero),
    map_pow, map_natCast]
  exact h2

end GlobalTheory.BSP
