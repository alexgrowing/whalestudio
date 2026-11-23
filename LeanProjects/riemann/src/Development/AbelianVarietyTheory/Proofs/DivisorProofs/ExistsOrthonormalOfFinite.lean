import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsOrthonormalBasisUnimodularHermitianLocalRi

open Matrix

namespace GlobalTheory.FiniteHermitian

theorem exists_pow_isIdempotentElem {R : Type} [Monoid R] [Finite R] (x : R) :
    ∃ m : ℕ, 0 < m ∧ IsIdempotentElem (x ^ m) := by
  have key : ∀ i d : ℕ, 0 < d → x ^ (i + d) = x ^ i → ∃ m : ℕ, 0 < m ∧ IsIdempotentElem (x ^ m) := by
    intro i d hd h
    have h1 : ∀ t k : ℕ, x ^ (i + k + t * d) = x ^ (i + k) := by
      intro t k
      induction t with
      | zero => simp
      | succ t ih =>
        have : i + k + (t + 1) * d = (i + d) + (k + t * d) := by ring
        rw [this, pow_add, h, ← pow_add, ← add_assoc, ih]
    have hle : i ≤ (i + 1) * d := by nlinarith
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
    refine ⟨(i + 1) * d, by positivity, ?_⟩
    unfold IsIdempotentElem
    rw [← pow_add]
    have := h1 (i + 1) k
    rw [← hk] at this
    exact this
  obtain ⟨i, j, hij, h⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => x ^ n)
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · exact key i (j - i) (by omega) (by rw [Nat.add_sub_cancel' hlt.le]; exact h.symm)
  · exact key j (i - j) (by omega) (by rw [Nat.add_sub_cancel' hlt.le]; exact h)

theorem isLocalRing_of_idempotent {R : Type} [CommRing R] [Finite R] [Nontrivial R]
    (h : ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1) : IsLocalRing R := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_
  obtain ⟨m, hm, he⟩ := exists_pow_isIdempotentElem x
  rcases h _ he with h0 | h1
  · exact Or.inr (IsNilpotent.isUnit_one_sub ⟨m, h0⟩)
  · exact Or.inl (IsUnit.of_pow_eq_one h1 hm.ne')

theorem cT_comb {R : Type} [CommRing R] (s : R →+* R) {n : ℕ} (c d : R)
    (A B : Matrix (Fin n) (Fin n) R) :
    ((c • A + d • B).map s).transpose = s c • (A.map s).transpose + s d • (B.map s).transpose := by
  ext i j
  simp

theorem exists_of_split {R : Type} [CommRing R] (s : R →+* R) (e : R)
    (he : IsIdempotentElem e) (hse : s e = 1 - e) {n : ℕ} (Q : Matrix (Fin n) (Fin n) R)
    (hQ : (Q.map s).transpose = Q) (hu : IsUnit Q) :
    ∃ a : Matrix (Fin n) (Fin n) R, (a.map s).transpose * Q * a = 1 := by
  obtain ⟨P, hP⟩ := hu.exists_right_inv
  have hP' : (P.map s).transpose * Q = 1 := by
    conv_lhs => rw [← hQ]
    rw [← Matrix.transpose_mul, ← Matrix.map_mul, hP]
    simp
  have h1 : ((1 : Matrix (Fin n) (Fin n) R).map s).transpose = 1 := by simp
  have hs1 : s (1 - e) = e := by rw [map_sub, map_one, hse]; ring
  have h01 : (1 - e) * e = 0 := by rw [sub_mul, one_mul, he.eq, sub_self]
  have h10 : e * (1 - e) = 0 := by rw [mul_comm, h01]
  have h11 : (1 - e) * (1 - e) = 1 - e := he.one_sub.eq
  refine ⟨e • P + (1 - e) • 1, ?_⟩
  rw [cT_comb, hs1, hse, h1]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, hP', hP,
    Matrix.one_mul, Matrix.mul_one, smul_add, smul_smul, h01, h10, h11, he.eq, zero_smul]
  rw [zero_add, add_zero, ← add_smul]
  simp

theorem exists_of_glue {R : Type} [CommRing R] (s : R →+* R) (e : R)
    (he : IsIdempotentElem e) (hse : s e = e) {n : ℕ} (Q A B : Matrix (Fin n) (Fin n) R)
    (hA : (1 - e) • ((A.map s).transpose * Q * A) = (1 - e) • (1 : Matrix (Fin n) (Fin n) R))
    (hB : e • ((B.map s).transpose * Q * B) = e • (1 : Matrix (Fin n) (Fin n) R)) :
    ∃ a : Matrix (Fin n) (Fin n) R, (a.map s).transpose * Q * a = 1 := by
  have hs1 : s (1 - e) = 1 - e := by rw [map_sub, map_one, hse]
  have h01 : (1 - e) * e = 0 := by rw [sub_mul, one_mul, he.eq, sub_self]
  have h10 : e * (1 - e) = 0 := by rw [mul_comm, h01]
  have h11 : (1 - e) * (1 - e) = 1 - e := he.one_sub.eq
  refine ⟨(1 - e) • A + e • B, ?_⟩
  rw [cT_comb, hs1, hse]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    smul_add, smul_smul, h01, h10, h11, he.eq, zero_smul]
  rw [zero_add, add_zero, hA, hB, ← add_smul]
  simp

def HasOrthonormal (R : Type) [CommRing R] : Prop :=
  ∀ s : R →+* R, (∀ x, s (s x) = x) → (∃ τ : R, τ + s τ = 1) →
    (∀ u : R, IsUnit u → s u = u → ∃ x : R, s x * x = u) →
    ∀ (n : ℕ) (Q : Matrix (Fin n) (Fin n) R), (Q.map s).transpose = Q → IsUnit Q →
      ∃ a : Matrix (Fin n) (Fin n) R, (a.map s).transpose * Q * a = 1

theorem exists_mod_idempotent {R : Type} [CommRing R] (s : R →+* R) (hs : ∀ x, s (s x) = x)
    (hτ : ∃ τ : R, τ + s τ = 1) (hn : ∀ u : R, IsUnit u → s u = u → ∃ x : R, s x * x = u)
    (e : R) (he : IsIdempotentElem e) (hse : s e = e)
    (ih : HasOrthonormal (R ⧸ Ideal.span {e}))
    {n : ℕ} (Q : Matrix (Fin n) (Fin n) R) (hQ : (Q.map s).transpose = Q) (hu : IsUnit Q) :
    ∃ A : Matrix (Fin n) (Fin n) R,
      (1 - e) • ((A.map s).transpose * Q * A) = (1 - e) • (1 : Matrix (Fin n) (Fin n) R) := by
  set I : Ideal R := Ideal.span {e} with hI
  let π : R →+* R ⧸ I := Ideal.Quotient.mk I
  have h01 : (1 - e) * e = 0 := by rw [sub_mul, one_mul, he.eq, sub_self]
  have hπe : π e = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self e)
  have hker : ∀ x y : R, π x = π y → (1 - e) * x = (1 - e) * y := by
    intro x y h
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 h)
    rw [← sub_eq_zero, ← mul_sub, ← hc, mul_left_comm, h01, mul_zero]
  let t : R ⧸ I →+* R ⧸ I := Ideal.Quotient.lift I (π.comp s) (by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [RingHom.comp_apply, map_mul, hse, map_mul, hπe, mul_zero])
  have ht : ∀ x, t (π x) = π (s x) := fun x => rfl
  have hsurj : Function.Surjective π := Ideal.Quotient.mk_surjective
  obtain ⟨a, ha⟩ := ih t
    (by intro x; obtain ⟨y, rfl⟩ := hsurj x; rw [ht, ht, hs])
    (by obtain ⟨τ, hτ⟩ := hτ; exact ⟨π τ, by rw [ht, ← map_add, hτ, map_one]⟩)
    (by
      intro u hu1 hu2
      obtain ⟨w, hw⟩ := hu1.exists_right_inv
      obtain ⟨u, rfl⟩ := hsurj u
      obtain ⟨w, rfl⟩ := hsurj w
      have e1 := hker (u * w) 1 (by rw [map_mul, hw, map_one])
      have e2 := hker (s u) u (by rw [← ht, hu2])
      have h11 : (1 - e) * (1 - e) = 1 - e := he.one_sub.eq
      have hee : e * e = e := he.eq
      obtain ⟨x, hx⟩ := hn ((1 - e) * u + e)
        (IsUnit.of_mul_eq_one ((1 - e) * w + e) (by
          linear_combination (u * w) * h11 + e1 + (u + w) * h01 + hee))
        (by rw [map_add, map_mul, map_sub, map_one, hse, e2])
      refine ⟨π x, ?_⟩
      rw [ht, ← map_mul, hx, map_add, map_mul, map_sub, map_one, hπe]
      ring)
    n (Q.map π)
    (by
      ext i j
      have := congrFun (congrFun hQ i) j
      simp only [Matrix.transpose_apply, Matrix.map_apply] at this ⊢
      rw [ht, this])
    (hu.map π.mapMatrix)
  choose σ hσ using hsurj
  have hA : (a.map σ).map π = a := by ext i j; simp [hσ]
  refine ⟨a.map σ, ?_⟩
  have hB : (((a.map σ).map s).transpose * Q * (a.map σ)).map π
      = (1 : Matrix (Fin n) (Fin n) R).map π := by
    have : (((a.map σ).map s).transpose).map π = (a.map t).transpose := by
      ext i j
      simp only [Matrix.transpose_apply, Matrix.map_apply]
      rw [← ht, hσ]
    rw [Matrix.map_mul, Matrix.map_mul, hA, this, ha, Matrix.map_one _ (map_zero π) (map_one π)]
  ext i j
  exact hker _ _ (congrFun (congrFun hB i) j)

theorem card_quot_lt {R : Type} [CommRing R] [Finite R] (e : R) (he : e ≠ 0) :
    Nat.card (R ⧸ Ideal.span {e}) < Nat.card R := by
  have hsurj : Function.Surjective (Ideal.Quotient.mk (Ideal.span {e})) :=
    Ideal.Quotient.mk_surjective
  refine lt_of_le_of_ne (Nat.card_le_card_of_surjective _ hsurj) fun h => he ?_
  have hb := (Nat.bijective_iff_surjective_and_card _).2 ⟨hsurj, h.symm⟩
  apply hb.1
  rw [map_zero]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self e)

theorem hasOrthonormal_of_finite (k : ℕ) :
    ∀ (R : Type) [CommRing R] [Finite R], Nat.card R = k → HasOrthonormal R := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro R _ _ hk s hs hτ hn n Q hQ hu
    haveI hfin : ∀ I : Ideal R, Finite (R ⧸ I) := fun I =>
      Finite.of_surjective _ (Ideal.Quotient.mk_surjective (I := I))
    by_cases h1 : ∃ e : R, IsIdempotentElem e ∧ s e = e ∧ e ≠ 0 ∧ e ≠ 1
    · obtain ⟨e, he, hse, h0, h1⟩ := h1
      obtain ⟨A, hA⟩ := exists_mod_idempotent s hs hτ hn e he hse
        (ih _ (hk ▸ card_quot_lt e h0) _ rfl) Q hQ hu
      obtain ⟨B, hB⟩ := exists_mod_idempotent s hs hτ hn (1 - e) he.one_sub
        (by rw [map_sub, map_one, hse])
        (ih _ (hk ▸ card_quot_lt (1 - e) (sub_ne_zero.2 h1.symm)) _ rfl) Q hQ hu
      rw [sub_sub_cancel] at hB
      exact exists_of_glue s e he hse Q A B hA hB
    · have hfix : ∀ e : R, IsIdempotentElem e → s e = e → e = 0 ∨ e = 1 := by
        intro e he hse
        by_contra hc
        push Not at hc
        exact h1 ⟨e, he, hse, hc.1, hc.2⟩
      by_cases h2 : ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1
      · rcases subsingleton_or_nontrivial R with hR | hR
        · exact ⟨1, Subsingleton.elim _ _⟩
        · haveI := isLocalRing_of_idempotent h2
          obtain ⟨a, ha⟩ :=
            GlobalTheory.Core.Rk.Exh.exists_orthonormal_of_isLocalRing R s hs hτ hn n Q hQ hu
          exact ⟨a.1, ha⟩
      · push Not at h2
        obtain ⟨e, he, h0, h1⟩ := h2
        have hee : e * e = e := he.eq
        have hff : s e * s e = s e := by rw [← map_mul, hee]
        have hz : e * s e = 0 := by
          rcases hfix (e * s e) (he.mul (he.map s)) (by rw [map_mul, hs, mul_comm]) with h | h
          · exact h
          · exact absurd (by linear_combination (1 - e) * h + s e * hee) h1
        have ho : e + s e = 1 := by
          rcases hfix (e + s e) (show (e + s e) * (e + s e) = e + s e by
            linear_combination hee + hff + 2 * hz) (by rw [map_add, hs, add_comm]) with h | h
          · exact absurd (by linear_combination e * h - hee - hz) h0
          · exact h
        exact exists_of_split s e he (by linear_combination ho) Q hQ hu

theorem exists_orthonormal_of_finite :
    ∀ (R : Type) [CommRing R] [Finite R] (s : R →+* R), (∀ x, s (s x) = x) → (∃ τ : R, τ + s τ = 1) → (∀ u : R, IsUnit u → s u = u → ∃ x : R, s x * x = u) → ∀ (n : ℕ) (Q : Matrix (Fin n) (Fin n) R), (Q.map s).transpose = Q → IsUnit Q → ∃ a : GL (Fin n) R, (a.1.map s).transpose * Q * a.1 = 1 := by
  intro R _ _ s hs hτ hn n Q hQ hu
  obtain ⟨a, ha⟩ := hasOrthonormal_of_finite _ R rfl s hs hτ hn n Q hQ hu
  have : IsUnit a := IsUnit.of_mul_eq_one_right _ ha
  exact ⟨this.unit, by rw [IsUnit.unit_spec]; exact ha⟩

end GlobalTheory.FiniteHermitian
