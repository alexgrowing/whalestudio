import Formalism.GradedWeylDivisibility.StatementE
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LHwlineLemmas
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LHwrowLemmas
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylDominanceOf

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem lehw_dom {r n : ℕ} (ν : Fin n → ℕ) (hnr : n ≤ r) (hν : Antitone ν)
    (f : MvPolynomial (Fin r × Fin n) ℚ) (hf : f ∈ dualWeyl ℚ r n ν) :
    ∀ m ∈ f.support, ∀ k : ℕ,
      (∑ a : Fin r with a.val < k, rowDeg m a) ≤ ∑ a : Fin r with a.val < k, rowNu (r := r) ν a := by
  classical
  intro m hm k
  let N : ℕ := ∏ d ∈ f.support, (coeff d f).den
  let u : MvPolynomial (Fin r × Fin n) ℤ := ∑ d ∈ f.support,
    monomial d ((∏ d' ∈ f.support.erase d, ((coeff d' f).den : ℤ)) * (coeff d f).num)
  have hu : map (Int.castRingHom ℚ) u = (N : ℚ) • f := by
    conv_rhs => rw [f.as_sum]
    rw [Finset.smul_sum]
    simp only [u, map_sum, map_monomial, smul_monomial]
    refine Finset.sum_congr rfl fun d hd => ?_
    congr 1
    push_cast
    have hN : (N : ℚ) = (∏ d' ∈ f.support.erase d, ((coeff d' f).den : ℚ)) * (coeff d f).den := by
      simp only [N]
      push_cast
      rw [Finset.prod_erase_mul _ _ hd]
    rw [smul_eq_mul, hN, mul_assoc, Rat.den_mul_eq_num]
    simp [eq_intCast]
  have hN0 : (N : ℚ) ≠ 0 := by
    simp only [N]
    push_cast
    exact Finset.prod_ne_zero_iff.mpr fun d _ => Nat.cast_ne_zero.mpr (coeff d f).den_nz
  have huD : u ∈ dualWeyl ℤ r n ν :=
    (dualWeylIntRat r n ν u).mpr (by rw [hu]; exact (dualWeyl ℚ r n ν).smul_mem _ hf)
  have hmu : m ∈ u.support := by
    rw [mem_support_iff]
    intro h0
    have e := congrArg (coeff m) hu
    rw [coeff_map, h0, map_zero, coeff_smul, smul_eq_mul] at e
    exact (mem_support_iff.mp hm) ((mul_eq_zero.mp e.symm).resolve_left hN0)
  exact (dualWeylDominanceZ r n ν hnr hν u huD m hmu).1 k

def LehwShift {R : Type*} [CommRing R] {r n : ℕ} (w : Fin r × Fin n → ℤ)
    (P : Polynomial (MvPolynomial (Fin r × Fin n) R)) (μ δ : ℤ) : Prop :=
  ∀ k : ℕ, IsWeightedHomogeneous w (P.coeff k) (μ + k * δ)

theorem lehwShift_mul {R : Type*} [CommRing R] {r n : ℕ} {w : Fin r × Fin n → ℤ}
    {P Q : Polynomial (MvPolynomial (Fin r × Fin n) R)} {μ μ' δ : ℤ}
    (hP : LehwShift w P μ δ) (hQ : LehwShift w Q μ' δ) : LehwShift w (P * Q) (μ + μ') δ := by
  intro k
  rw [Polynomial.coeff_mul]
  refine (mem_weightedHomogeneousSubmodule _ _ _ _).mp (Submodule.sum_mem _ fun x hx => ?_)
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  refine (mem_weightedHomogeneousSubmodule _ _ _ _).mpr ?_
  have h := (hP x.1).mul (hQ x.2)
  convert h using 1
  rw [← hx]
  push_cast
  ring

theorem lehwShift_one {R : Type*} [CommRing R] {r n : ℕ} (w : Fin r × Fin n → ℤ) (δ : ℤ) :
    LehwShift w (1 : Polynomial (MvPolynomial (Fin r × Fin n) R)) 0 δ := by
  intro k
  by_cases hk : k = 0
  · subst hk
    rw [Polynomial.coeff_one_zero]
    intro d hd
    rw [MvPolynomial.coeff_one] at hd
    split_ifs at hd with h
    · subst h
      simp
    · exact (hd rfl).elim
  · rw [Polynomial.coeff_one, if_neg (by omega)]
    intro d hd
    exact (hd (MvPolynomial.coeff_zero d)).elim

theorem lehwShift_pow {R : Type*} [CommRing R] {r n : ℕ} {w : Fin r × Fin n → ℤ}
    {P : Polynomial (MvPolynomial (Fin r × Fin n) R)} {μ δ : ℤ}
    (hP : LehwShift w P μ δ) (e : ℕ) : LehwShift w (P ^ e) (e • μ) δ := by
  induction e with
  | zero => simpa using lehwShift_one (R := R) w δ
  | succ e ih =>
    rw [pow_succ, succ_nsmul]
    exact lehwShift_mul ih hP

theorem lehwShift_prod {R : Type*} [CommRing R] {r n : ℕ} {w : Fin r × Fin n → ℤ} {ι : Type*}
    (s : Finset ι) (P : ι → Polynomial (MvPolynomial (Fin r × Fin n) R)) (μ : ι → ℤ) (δ : ℤ)
    (h : ∀ i ∈ s, LehwShift w (P i) (μ i) δ) : LehwShift w (∏ i ∈ s, P i) (∑ i ∈ s, μ i) δ := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    simpa using lehwShift_one (R := R) w δ
  · intro i s hi ih h
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact lehwShift_mul (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem lehwShift_algebraMap {R : Type*} [CommRing R] {r n : ℕ} (w : Fin r × Fin n → ℤ) (c : R) (δ : ℤ) :
    LehwShift w (algebraMap R (Polynomial (MvPolynomial (Fin r × Fin n) R)) c) 0 δ := by
  intro k
  have h1 := lehwShift_one (R := R) w δ k
  rw [Algebra.algebraMap_eq_smul_one, Polynomial.coeff_smul]
  exact (mem_weightedHomogeneousSubmodule _ _ _ _).mp
    (Submodule.smul_mem _ c ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr h1))

theorem lehwShift_gen {R : Type*} [CommRing R] {r n : ℕ} (w : Fin r × Fin n → ℤ) (δ : ℤ)
    (a b : Fin r) (hstep : ∀ s : Fin n, w (a, s) = w (b, s) + δ) (v : Fin r × Fin n) :
    LehwShift w (Polynomial.C (X v) +
      (if v.1 = b then Polynomial.X * Polynomial.C (X (a, v.2)) else 0) :
        Polynomial (MvPolynomial (Fin r × Fin n) R)) (w v) δ := by
  obtain ⟨c, s⟩ := v
  intro k
  by_cases hc : c = b
  · subst hc
    rw [if_pos (show (c, s).1 = c from rfl)]
    rcases k with _ | _ | k
    · have e : (Polynomial.C (X (c, s)) + Polynomial.X * Polynomial.C (X (a, s)) :
          Polynomial (MvPolynomial (Fin r × Fin n) R)).coeff 0 = X (c, s) := by simp
      rw [e]
      simpa using isWeightedHomogeneous_X R w (c, s)
    · have e : (Polynomial.C (X (c, s)) + Polynomial.X * Polynomial.C (X (a, s)) :
          Polynomial (MvPolynomial (Fin r × Fin n) R)).coeff (0 + 1) = X (a, s) := by simp
      rw [e]
      convert isWeightedHomogeneous_X R w (a, s) using 1
      rw [hstep s]
      push_cast
      ring
    · have e : (Polynomial.C (X (c, s)) + Polynomial.X * Polynomial.C (X (a, s)) :
          Polynomial (MvPolynomial (Fin r × Fin n) R)).coeff (k + 1 + 1) = 0 := by
        simp [Polynomial.coeff_C]
      rw [e]
      intro d hd
      exact (hd (MvPolynomial.coeff_zero d)).elim
  · rw [if_neg (show ¬ (c, s).1 = b from hc), add_zero, Polynomial.coeff_C]
    split_ifs with hk
    · subst hk
      simpa using isWeightedHomogeneous_X R w (c, s)
    · intro d hd
      exact (hd (MvPolynomial.coeff_zero d)).elim

theorem lehwShift_rowGen_monomial (R : Type*) [CommRing R] {r n : ℕ} (w : Fin r × Fin n → ℤ) (δ : ℤ)
    (a b : Fin r) (hstep : ∀ s : Fin n, w (a, s) = w (b, s) + δ) (d : Fin r × Fin n →₀ ℕ) (c : R) :
    LehwShift w (rowGen R a b (monomial d c)) (Finsupp.weight w d) δ := by
  unfold rowGen
  rw [MvPolynomial.aeval_monomial, Finsupp.weight_apply]
  have h := lehwShift_mul (lehwShift_algebraMap (R := R) w c δ)
    (lehwShift_prod d.support _ (fun v => d v • w v) δ
      (fun v _ => lehwShift_pow (lehwShift_gen (R := R) w δ a b hstep v) (d v)))
  simpa [Finsupp.prod, Finsupp.sum] using h

theorem lehw_rowDiv_shift (R : Type*) [CommRing R] {r n : ℕ} (w : Fin r × Fin n → ℤ) (δ : ℤ)
    (a b : Fin r) (hstep : ∀ s : Fin n, w (a, s) = w (b, s) + δ) (H : ℤ) (k : ℕ)
    (f : MvPolynomial (Fin r × Fin n) R) (hf : IsWeightedHomogeneous w f H) :
    IsWeightedHomogeneous w (rowDiv R a b k f) (H + k * δ) := by
  unfold rowDiv
  rw [f.as_sum, map_sum, Polynomial.finset_sum_coeff]
  refine (mem_weightedHomogeneousSubmodule _ _ _ _).mp (Submodule.sum_mem _ fun d hd => ?_)
  refine (mem_weightedHomogeneousSubmodule _ _ _ _).mpr ?_
  have h := lehwShift_rowGen_monomial R w δ a b hstep d (coeff d f) k
  rw [hf (mem_support_iff.mp hd)] at h
  exact h

def lehwP {r n : ℕ} (a : Fin r) : Fin r × Fin n → ℤ := fun v => if v.1.val ≤ a.val then 1 else 0

theorem highestWeightCount_self_eq_succ_of_lt {r n : ℕ} {a b : Fin r} (hab : a < b) (s : Fin n) :
    lehwP (n := n) a (a, s) = lehwP a (b, s) + 1 := by
  have h : a.val < b.val := hab
  simp [lehwP, show ¬ b.val ≤ a.val by omega]

theorem lehw_weight_P {r n : ℕ} (a : Fin r) (m : Fin r × Fin n →₀ ℕ) :
    Finsupp.weight (lehwP a) m = ((∑ a' : Fin r with a'.val < a.val + 1, rowDeg m a' : ℕ) : ℤ) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_prod_type]
  push_cast
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun a' _ => ?_
  simp only [rowDeg, lehwP]
  by_cases h : a'.val ≤ a.val
  · simp [h, show a'.val < a.val + 1 by omega]
  · simp [h, show ¬ a'.val < a.val + 1 by omega]

theorem lehw_weight_rowW {r n : ℕ} (m : Fin r × Fin n →₀ ℕ) (a : Fin r) :
    Finsupp.weight (rowW r n) m a = rowDeg m a := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply,
    Fintype.sum_prod_type]
  simp only [rowW, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single a]
  · simp [rowDeg]
  · intro b _ hb
    simp [hb, Ne.symm hb]
  · simp

theorem lehw_kill {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν)
    (G : MvPolynomial (Fin r × Fin n) ℚ) (hG : G ∈ dualWeyl ℚ r n ν)
    (hGh : IsWeightedHomogeneous (rowW r n) G (rowNu (r := r) ν))
    (a b : Fin r) (hab : a < b) (k : ℕ) (hk : 1 ≤ k) : rowDiv ℚ a b k G = 0 := by
  have hH := rowDivStable ℚ r n ν a b k G hG
  by_contra hne
  obtain ⟨m, hm⟩ := MvPolynomial.ne_zero_iff.mp hne
  have hGP : IsWeightedHomogeneous (lehwP (n := n) a) G
      ((∑ a' : Fin r with a'.val < a.val + 1, rowNu (r := r) ν a' : ℕ) : ℤ) := by
    intro d hd
    rw [lehw_weight_P]
    congr 1
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [← lehw_weight_rowW, hGh hd]
  have hshift := lehw_rowDiv_shift ℚ (lehwP a) 1 a b (highestWeightCount_self_eq_succ_of_lt hab) _ k G hGP
  have hmw := hshift hm
  rw [lehw_weight_P] at hmw
  have hdom := lehw_dom ν hn hν _ hH m (mem_support_iff.mpr hm) (a.val + 1)
  omega

end Formalism.GradedWeylDivisibility
