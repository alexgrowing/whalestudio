import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExcisionNbhdSelf
open Polynomial GlobalTheory.EtC

namespace GlobalTheory

theorem exists_algebraMap_sub_mem_of_isMaximal_of_isAlgClosed (k B : Type) [Field k] [IsAlgClosed k]
    [CommRing B] [Algebra k B] [Algebra.FiniteType k B] (P : Ideal B) [hP : P.IsMaximal] (b : B) :
    ∃ c : k, b - algebraMap k B c ∈ P := by
  letI := Ideal.Quotient.field P
  haveI : Module.Finite k (B ⧸ P) := finite_of_finite_type_of_isJacobsonRing k (B ⧸ P)
  let φ : (B ⧸ P) →ₐ[k] k := IsAlgClosed.lift
  refine ⟨φ (Ideal.Quotient.mk P b), ?_⟩
  have h : algebraMap k (B ⧸ P) (φ (Ideal.Quotient.mk P b)) = Ideal.Quotient.mk P b := by
    apply φ.toRingHom.injective
    simp
  have h2 : Ideal.Quotient.mk P (algebraMap k B (φ (Ideal.Quotient.mk P b))) =
      algebraMap k (B ⧸ P) (φ (Ideal.Quotient.mk P b)) := rfl
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, h2, h, sub_self]

theorem exists_pow_sub_mem_pow_of_isMaximal_of_isAlgClosed (k B : Type) [Field k] [IsAlgClosed k]
    [CommRing B] [Algebra k B] [Algebra.FiniteType k B] (q : ℕ) (hq : IsUnit (q : k))
    (P : Ideal B) [hP : P.IsMaximal] (b : B) (hb : b ∉ P) :
    ∀ m : ℕ, ∃ r : B, b - r ^ q ∈ P ^ (m + 1) := by
  have hq0 : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · subst h; simp at hq
    · exact h
  have hqB : IsUnit (q : B) := by
    have := hq.map (algebraMap k B); simpa using this
  intro m
  induction m with
  | zero =>
    obtain ⟨c, hc⟩ := exists_algebraMap_sub_mem_of_isMaximal_of_isAlgClosed k B P b
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq c hq0
    refine ⟨algebraMap k B z, ?_⟩
    rw [← map_pow, hz]; simpa using hc
  | succ m ih =>
    obtain ⟨r, hr⟩ := ih
    obtain ⟨e, he⟩ : ∃ e, e = b - r ^ q := ⟨_, rfl⟩
    rw [← he] at hr
    have hrP : r ∉ P := by
      intro h
      apply hb
      have h1 : r ^ q ∈ P := P.pow_mem_of_mem h q hq0
      have h2 : e ∈ P := Ideal.pow_le_self (Nat.succ_ne_zero m) hr
      have : b = e + r ^ q := by rw [he]; ring
      rw [this]; exact P.add_mem h2 h1
    have hderP : (q : B) * r ^ (q - 1) ∉ P := by
      intro h
      rcases hP.isPrime.mem_or_mem h with h | h
      · exact hP.ne_top (Ideal.eq_top_of_isUnit_mem P h hqB)
      · exact hrP (hP.isPrime.mem_of_pow_mem _ h)
    obtain ⟨w, i, hi, hw⟩ := hP.exists_inv hderP
    obtain ⟨t, ht⟩ := binomExpansion (X ^ q : B[X]) r (e * w)
    simp [derivative_X_pow] at ht
    refine ⟨r + e * w, ?_⟩
    have key : b - (r + e * w) ^ q = e * i - t * w ^ 2 * e ^ 2 := by
      rw [ht]; linear_combination (-e) * hw - he
    rw [key]
    refine Ideal.sub_mem _ ?_ ?_
    · rw [pow_succ]; exact Ideal.mul_mem_mul hr hi
    · apply Ideal.mul_mem_left
      have h3 : e ^ 2 ∈ (P ^ (m + 1)) ^ 2 := Ideal.pow_mem_pow hr 2
      rw [← pow_mul] at h3
      exact Ideal.pow_le_pow_right (by omega) h3

theorem exists_pow_sub_mem_span_of_isUnit_mod_of_isAlgClosed : ∀ (k B : Type) [Field k] [IsAlgClosed k]
    [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B] (q : ℕ),
    IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ b c : B, b * c - 1 ∈ Ideal.span {f} →
      ∃ r : B, b - r ^ q ∈ Ideal.span {f} := by
  intro k B _ _ _ _ _ _ q hq f hf b c hbc
  classical
  have hI : Ideal.span {f} ≠ ⊥ := by simpa [Ideal.span_singleton_eq_bot] using hf
  have hroot : ∀ P : (UniqueFactorizationMonoid.factors (Ideal.span {f})).toFinset, ∃ r : B,
      b - r ^ q ∈ (P : Ideal B) ^ Multiset.count (P : Ideal B)
        (UniqueFactorizationMonoid.factors (Ideal.span {f})) := by
    intro P
    have hmem := Multiset.mem_toFinset.mp P.prop
    have hprime : Prime (P : Ideal B) := UniqueFactorizationMonoid.prime_of_factor _ hmem
    have hne : (P : Ideal B) ≠ ⊥ := hprime.ne_zero
    haveI hmax : (P : Ideal B).IsMaximal := (Ideal.isPrime_of_prime hprime).isMaximal hne
    have hle : Ideal.span {f} ≤ (P : Ideal B) :=
      Ideal.le_of_dvd (UniqueFactorizationMonoid.dvd_of_mem_factors hmem)
    have hb : b ∉ (P : Ideal B) := by
      intro h
      apply hmax.ne_top
      rw [Ideal.eq_top_iff_one]
      have h1 := hle hbc
      have : (1 : B) = b * c - (b * c - 1) := by ring
      rw [this]; exact Ideal.sub_mem _ (Ideal.mul_mem_right _ _ h) h1
    obtain ⟨r, hr⟩ := exists_pow_sub_mem_pow_of_isMaximal_of_isAlgClosed k B q hq (P : Ideal B) b hb
      (Multiset.count (P : Ideal B) (UniqueFactorizationMonoid.factors (Ideal.span {f})))
    exact ⟨r, Ideal.pow_le_pow_right (Nat.le_succ _) hr⟩
  choose r hr using hroot
  obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective
    ((IsDedekindDomain.quotientEquivPiFactors hI).symm (fun P => Ideal.Quotient.mk _ (r P)))
  refine ⟨s, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  apply (IsDedekindDomain.quotientEquivPiFactors hI).injective
  rw [map_zero]
  funext P
  have h1 := congrFun (congrArg (IsDedekindDomain.quotientEquivPiFactors hI) hs) P
  rw [RingEquiv.apply_symm_apply, IsDedekindDomain.quotientEquivPiFactors_mk] at h1
  simp only at h1
  rw [IsDedekindDomain.quotientEquivPiFactors_mk]
  show Ideal.Quotient.mk _ (b - s ^ q) = 0
  rw [map_sub, map_pow, h1, ← map_pow, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  exact hr P

end GlobalTheory
