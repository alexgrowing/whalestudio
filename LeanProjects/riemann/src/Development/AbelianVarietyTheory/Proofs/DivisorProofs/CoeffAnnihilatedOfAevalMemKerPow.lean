import Mathlib
open scoped TensorProduct

namespace GlobalTheory.TriangularityLowCoeff

open MvPolynomial

noncomputable def iterDer {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {d : ℕ}
    (D : Fin d → Derivation R A A) : List (Fin d) → A →ₗ[R] A
  | [] => LinearMap.id
  | i :: L => (iterDer D L) ∘ₗ (D i).toLinearMap

noncomputable def expOf {d : ℕ} (L : List (Fin d)) : Fin d →₀ ℕ :=
  Multiset.toFinsupp (L : Multiset (Fin d))

noncomputable def fac {d : ℕ} : List (Fin d) → (Fin d →₀ ℕ) → ℕ
  | [], _ => 1
  | i :: L, m => ((m + expOf L) i + 1) * fac L m

theorem expOf_cons {d : ℕ} (i : Fin d) (L : List (Fin d)) :
    expOf (i :: L) = Finsupp.single i 1 + expOf L := by
  rw [expOf, ← Multiset.cons_coe, ← Multiset.singleton_add, Multiset.toFinsupp_add,
    Multiset.toFinsupp_singleton, expOf]

theorem degree_expOf {d : ℕ} (L : List (Fin d)) : (expOf L).degree = L.length := by
  induction L with
  | nil => simp [expOf]
  | cons i L ih => rw [expOf_cons, map_add, ih, Finsupp.degree_single]; simp; omega

theorem expOf_apply_le {d : ℕ} (L : List (Fin d)) (i : Fin d) : expOf L i ≤ L.length := by
  rw [expOf, Multiset.toFinsupp_apply, Multiset.coe_count]
  exact List.count_le_length

theorem expOf_toList {d : ℕ} (α : Fin d →₀ ℕ) : expOf (Finsupp.toMultiset α).toList = α := by
  rw [expOf, Multiset.coe_toList, Finsupp.toMultiset_toFinsupp]

theorem fac_dvd {d : ℕ} (L : List (Fin d)) : fac L 0 ∣ (L.length).factorial ^ L.length := by
  induction L with
  | nil => simp [fac]
  | cons i L ih =>
    simp only [fac, zero_add, List.length_cons]
    rw [pow_succ']
    refine mul_dvd_mul (Nat.dvd_factorial (by omega) (by have := expOf_apply_le L i; omega)) ?_
    exact ih.trans (pow_dvd_pow_of_dvd (Nat.factorial_dvd_factorial (by omega)) _)

theorem der_mem_pow {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
    (D : Derivation R A A) (J : Ideal A) : ∀ (k : ℕ) (x : A), x ∈ J ^ (k + 1) → D x ∈ J ^ k
  | 0, x, _ => by simp
  | k + 1, x, hx => by
    rw [pow_succ'] at hx
    refine Submodule.mul_induction_on (C := fun x => D x ∈ J ^ (k + 1)) hx ?_ ?_
    · intro a ha b hb
      rw [D.leibniz, smul_eq_mul, smul_eq_mul]
      refine Ideal.add_mem _ ?_ (Ideal.mul_mem_right _ _ hb)
      rw [pow_succ']
      exact Ideal.mul_mem_mul ha (der_mem_pow D J k b hb)
    · intro x y hx hy
      rw [map_add]
      exact Ideal.add_mem _ hx hy

theorem iterDer_mem {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {d : ℕ}
    (D : Fin d → Derivation R A A) (J : Ideal A) :
    ∀ (L : List (Fin d)) (m : ℕ) (x : A), x ∈ J ^ (L.length + m) → iterDer D L x ∈ J ^ m
  | [], m, x, hx => by simpa [iterDer] using hx
  | i :: L, m, x, hx => by
    show iterDer D L (D i x) ∈ J ^ m
    apply iterDer_mem D J L m
    apply der_mem_pow (D i) J
    have e : L.length + m + 1 = (i :: L).length + m := by simp; omega
    rw [e]; exact hx

theorem der_aeval {R B : Type} [CommRing R] [CommRing B] [Algebra R B] {d : ℕ}
    (D : Derivation R B B) (y : Fin d → B) (Q : MvPolynomial (Fin d) R) :
    D (aeval y Q) = ∑ j, aeval y (pderiv j Q) * D (y j) := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [map_add, hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p i hp =>
    rw [map_mul, aeval_X, D.leibniz, hp, smul_eq_mul, smul_eq_mul]
    simp only [pderiv_mul, pderiv_X, map_add, map_mul, aeval_X, add_mul, Finset.sum_add_distrib,
      Finset.mul_sum]
    rw [add_comm]
    congr 1
    · exact Finset.sum_congr rfl fun j _ => by ring
    · rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj; simp [Pi.single_apply, hj]
      · simp

theorem coeff_iterPD {R : Type} [CommRing R] {d : ℕ} :
    ∀ (L : List (Fin d)) (m : Fin d →₀ ℕ) (Q : MvPolynomial (Fin d) R),
      coeff m (iterDer (fun i => pderiv i) L Q) = coeff (m + expOf L) Q * (fac L m : R)
  | [], m, Q => by simp [iterDer, expOf, fac]
  | i :: L, m, Q => by
    show coeff m (iterDer (fun i => pderiv i) L (pderiv i Q)) = _
    rw [coeff_iterPD L m, coeff_pderiv, fac, expOf_cons]
    have e : m + expOf L + Finsupp.single i 1 = m + (Finsupp.single i 1 + expOf L) := by abel
    rw [e]; push_cast; ring

theorem aeval_mem_pow {R B : Type} [CommRing R] [CommRing B] [Algebra R B] {d : ℕ}
    (ε : B →ₐ[R] R) (y : Fin d → B) (hy : ∀ i, ε (y i) = 0) (n : ℕ) (Q : MvPolynomial (Fin d) R)
    (hQ : Q ∈ idealOfVars (Fin d) R ^ n) : aeval y Q ∈ RingHom.ker ε ^ n := by
  have h1 : Ideal.map (aeval y) (idealOfVars (Fin d) R) ≤ RingHom.ker ε := by
    rw [idealOfVars, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    simp [RingHom.mem_ker, hy]
  have h2 := Ideal.mem_map_of_mem (aeval y) hQ
  rw [Ideal.map_pow] at h2
  exact Ideal.pow_right_mono h1 n h2

theorem eval_aeval {R B : Type} [CommRing R] [CommRing B] [Algebra R B] {d : ℕ}
    (ε : B →ₐ[R] R) (y : Fin d → B) (hy : ∀ i, ε (y i) = 0) (Q : MvPolynomial (Fin d) R) :
    ε (aeval y Q) = coeff 0 Q := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hy, coeff_mul_X']

theorem eval_iterDer_aeval {R B : Type} [CommRing R] [CommRing B] [Algebra R B] {d : ℕ}
    (ε : B →ₐ[R] R) (y : Fin d → B) (D : Fin d → Derivation R B B)
    (hy : ∀ i, ε (y i) = 0) (hD : ∀ i j, ε (D i (y j)) = if i = j then 1 else 0) :
    ∀ (L : List (Fin d)) (Q : MvPolynomial (Fin d) R), Q ∈ idealOfVars (Fin d) R ^ L.length →
      ε (iterDer D L (aeval y Q)) = coeff 0 (iterDer (fun i => pderiv i) L Q)
  | [], Q, _ => by simpa [iterDer] using eval_aeval ε y hy Q
  | i :: L, Q, hQ => by
    show ε (iterDer D L (D i (aeval y Q))) = coeff 0 (iterDer (fun i => pderiv i) L (pderiv i Q))
    have hP : ∀ j, pderiv j Q ∈ idealOfVars (Fin d) R ^ L.length := fun j =>
      der_mem_pow (pderiv j) _ L.length Q (by simpa using hQ)
    have key : ∀ j, ε (iterDer D L (aeval y (pderiv j Q) * D i (y j))) =
        ε (D i (y j)) * coeff 0 (iterDer (fun i => pderiv i) L (pderiv j Q)) := by
      intro j
      set x := aeval y (pderiv j Q)
      set u := D i (y j)
      have split : x * u = ε u • x + x * (u - algebraMap R B (ε u)) := by
        rw [Algebra.smul_def]; ring
      have hmem : x * (u - algebraMap R B (ε u)) ∈ RingHom.ker ε ^ (L.length + 1) := by
        rw [pow_succ]
        refine Ideal.mul_mem_mul (aeval_mem_pow ε y hy _ _ (hP j)) ?_
        simp [RingHom.mem_ker]
      have h0 : ε (iterDer D L (x * (u - algebraMap R B (ε u)))) = 0 := by
        have := iterDer_mem D (RingHom.ker ε) L 1 _ hmem
        rw [pow_one, RingHom.mem_ker] at this
        exact this
      rw [split, map_add, map_add, h0, add_zero, map_smul, map_smul, smul_eq_mul,
        eval_iterDer_aeval ε y D hy hD L (pderiv j Q) (hP j)]
    rw [der_aeval, map_sum, map_sum]
    simp only [key, hD, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem exists_mul_coeff_eq_zero (d N : ℕ) : ∃ K : ℕ, 0 < K ∧ ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B]
    (ε : B →ₐ[R] R) (y : Fin d → B) (D : Fin d → Derivation R B B), (∀ i, ε (y i) = 0) →
    (∀ i j, ε (D i (y j)) = if i = j then 1 else 0) → ∀ P : MvPolynomial (Fin d) R,
    (∀ α : Fin d →₀ ℕ, N ≤ α.degree → MvPolynomial.coeff α P = 0) →
    MvPolynomial.aeval y P ∈ RingHom.ker ε ^ N → ∀ α, (K : R) * MvPolynomial.coeff α P = 0 := by
  refine ⟨(N.factorial ^ N) ^ N, by positivity, ?_⟩
  intro R B _ _ _ ε y D hy hD P hhi hP
  set c : ℕ := N.factorial ^ N with hc
  have claim : ∀ k, k ≤ N → ∀ α : Fin d →₀ ℕ, α.degree < k → ((c ^ k : ℕ) : R) * coeff α P = 0 := by
    intro k
    induction k with
    | zero => intro _ α h; omega
    | succ k ih =>
      intro hk α hα
      rcases Nat.lt_or_ge α.degree k with h | h
      · rw [pow_succ, Nat.cast_mul, mul_comm ((c ^ k : ℕ) : R), mul_assoc, ih (by omega) α h, mul_zero]
      · have hdeg : α.degree = k := by omega
        set L := (Finsupp.toMultiset α).toList
        have hL : expOf L = α := expOf_toList α
        have hlen : L.length = k := by rw [← degree_expOf, hL, hdeg]
        set P' := C ((c ^ k : ℕ) : R) * P
        have hP'1 : P' ∈ idealOfVars (Fin d) R ^ L.length := by
          rw [mem_pow_idealOfVars_iff', hlen]
          intro β hβ
          rw [coeff_C_mul, ih (by omega) β hβ]
        have hP'2 : aeval y P' ∈ RingHom.ker ε ^ (L.length + 1) := by
          rw [map_mul]
          refine Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right (by omega) hP)
        have e1 := eval_iterDer_aeval ε y D hy hD L P' hP'1
        have e2 := iterDer_mem D (RingHom.ker ε) L 1 _ hP'2
        rw [pow_one, RingHom.mem_ker, e1, coeff_iterPD, zero_add, hL, coeff_C_mul] at e2
        obtain ⟨g, hg⟩ : fac L 0 ∣ c := by
          refine (fac_dvd L).trans ?_
          rw [hc, hlen]
          exact (pow_dvd_pow_of_dvd (Nat.factorial_dvd_factorial (by omega)) k).trans
            (pow_dvd_pow _ (by omega))
        have hg' : (c : R) = (fac L 0 : R) * (g : R) := by rw [hg, Nat.cast_mul]
        push_cast at e2
        calc ((c ^ (k + 1) : ℕ) : R) * coeff α P = (c : R) ^ k * (c : R) * coeff α P := by
              push_cast; ring
          _ = (c : R) ^ k * ((fac L 0 : R) * (g : R)) * coeff α P := by rw [← hg']
          _ = ((c : R) ^ k * coeff α P * (fac L 0 : R)) * g := by ring
          _ = 0 := by rw [e2, zero_mul]
  intro α
  rcases Nat.lt_or_ge α.degree N with h | h
  · exact claim N le_rfl α h
  · rw [hhi α h, mul_zero]

end GlobalTheory.TriangularityLowCoeff
