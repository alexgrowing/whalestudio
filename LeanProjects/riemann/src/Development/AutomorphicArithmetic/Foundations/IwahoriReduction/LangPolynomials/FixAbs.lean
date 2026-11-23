import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.FixedIntegersIsUnitOfNotMemPrimeSpan

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

private theorem exists_natCast_add_mul_of_frobenius_fixed {R : Type} [CommRing R] [IsDomain R] (p : ℕ) [hp : Fact p.Prime]
    (σ : R ≃+* R) (hpr : Prime (p : R)) (hfrob : ∀ x : R, σ x - x ^ p ∈ Ideal.span {(p : R)})
    (x : R) (hx : σ x = x) : ∃ a : ℕ, ∃ y : R, x = a + p * y ∧ σ y = y := by
  classical
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  haveI : (Ideal.span {(p : R)}).IsPrime := (Ideal.span_singleton_prime hpr.ne_zero).mpr hpr
  haveI : CharP (R ⧸ Ideal.span {(p : R)}) p := CharP.quotient R p (mem_nonunits_iff.mpr hpr.not_unit)
  let K := R ⧸ Ideal.span {(p : R)}
  let π : R →+* K := Ideal.Quotient.mk _
  let f : ZMod p →+* K := ZMod.castHom (dvd_refl p) K
  have hxx : π x ^ p = π x := by
    have h1 := hfrob x
    rw [hx] at h1
    have h2 : π (x - x ^ p) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr h1
    rw [map_sub, map_pow] at h2
    exact (sub_eq_zero.mp h2).symm
  have hf : Function.Injective f := f.injective
  let q : Polynomial K := Polynomial.X ^ p - Polynomial.X
  have hdeg : q.natDegree = p := by
    have h1 : (Polynomial.X : Polynomial K).natDegree < (Polynomial.X ^ p : Polynomial K).natDegree := by
      rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_X]
      exact hp.out.one_lt
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt h1, Polynomial.natDegree_X_pow]
  have hq : q ≠ 0 := by
    intro h
    have := hdeg
    rw [h, Polynomial.natDegree_zero] at this
    exact hp.out.ne_zero this.symm
  have hroot : ∀ t : K, t ^ p = t → t ∈ q.roots.toFinset := by
    intro t ht
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hq]
    simp [q, ht]
  have hsub : Finset.univ.image f ⊆ q.roots.toFinset := by
    intro t ht
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp ht
    apply hroot
    rw [← map_pow, ZMod.pow_card]
  have hcard : q.roots.toFinset.card ≤ (Finset.univ.image f).card := by
    rw [Finset.card_image_of_injective _ hf, Finset.card_univ, ZMod.card]
    calc q.roots.toFinset.card ≤ Multiset.card q.roots := Multiset.toFinset_card_le _
      _ ≤ q.natDegree := Polynomial.card_roots' q
      _ = p := hdeg
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  have hmem : π x ∈ Finset.univ.image f := heq ▸ hroot _ hxx
  obtain ⟨a, -, ha⟩ := Finset.mem_image.mp hmem
  have hval : π (a.val : R) = π x := by
    rw [map_natCast, ZMod.natCast_val, ← ha]
    rfl
  have hmemI : x - (a.val : R) ∈ Ideal.span {(p : R)} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    change π (x - (a.val : R)) = 0
    rw [map_sub, hval, sub_self]
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hmemI
  refine ⟨a.val, y, by rw [mul_comm, hy]; ring, ?_⟩
  have h3 : (p : R) * σ y = p * y := by
    have := congrArg σ hy
    rw [map_mul, map_natCast, map_sub, map_natCast, hx] at this
    rw [mul_comm, this, mul_comm, hy]
  exact mul_left_cancel₀ hpr.ne_zero h3

theorem UpperTheory.Kd.C7.pFixAbs :
    UpperTheory.Kd.C7.SFixAbs := by
  intro R _ p _ _ σ hσ x hx
  obtain ⟨hdom, hpr, hcomp, hfrob, -⟩ := hσ
  classical
  haveI := hdom
  haveI := hcomp
  have step : ∀ y : {y : R // σ y = y}, ∃ a : ℕ, ∃ y' : {y : R // σ y = y}, y.1 = a + p * y'.1 := by
    intro y
    obtain ⟨a, y', h1, h2⟩ := exists_natCast_add_mul_of_frobenius_fixed p σ hpr hfrob y.1 y.2
    exact ⟨a, ⟨y', h2⟩, h1⟩
  choose d nx hdn using step
  let seq : ℕ → {y : R // σ y = y} := fun n => Nat.rec ⟨x, hx⟩ (fun _ y => nx y) n
  let s : ℕ → ℕ := fun n => ∑ i ∈ Finset.range n, d (seq i) * p ^ i
  have hrep : ∀ n, x = (s n : R) + (p : R) ^ n * (seq n).1 := by
    intro n
    induction n with
    | zero => simp [s, seq]
    | succ n ih =>
      have e : seq (n + 1) = nx (seq n) := rfl
      rw [ih, hdn (seq n)]
      simp only [s, Finset.sum_range_succ, e]
      push_cast
      ring
  have hdvd : ∀ m k, (p : ℤ) ^ m ∣ ((s (m + k) : ℕ) : ℤ) - (s m : ℤ) := by
    intro m k
    induction k with
    | zero => simp
    | succ k ih =>
      have e : ((s (m + (k + 1)) : ℕ) : ℤ) - s m
          = (((s (m + k)) : ℤ) - s m) + (d (seq (m + k)) : ℤ) * (p : ℤ) ^ (m + k) := by
        simp only [s, ← add_assoc, Finset.sum_range_succ]
        push_cast
        ring
      rw [e]
      exact dvd_add ih (Dvd.dvd.mul_left (pow_dvd_pow _ (Nat.le_add_right _ _)) _)
  have hZ : ∀ (a b : ℤ_[p]) (m : ℕ), a ≡ b [SMOD ((IsLocalRing.maximalIdeal ℤ_[p]) ^ m • ⊤ : Submodule ℤ_[p] ℤ_[p])]
      ↔ (p : ℤ_[p]) ^ m ∣ a - b := by
    intro a b m
    rw [SModEq.sub_mem, PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow, Ideal.smul_eq_mul,
      Ideal.mul_top, Ideal.mem_span_singleton]
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := IsLocalRing.maximalIdeal ℤ_[p]) inferInstance
    (f := fun n => (s n : ℤ_[p])) (by
      intro m n hmn
      rw [hZ]
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
      have h1 := map_dvd (Int.castRingHom ℤ_[p]) (hdvd m k)
      simp only [map_pow, map_sub, map_natCast] at h1
      rw [← dvd_neg, neg_sub]
      exact h1)
  refine ⟨L, ?_⟩
  rw [IsHausdorff.eq_iff_smodEq (I := Ideal.span {(p : R)})]
  intro n
  rw [SModEq.sub_mem, Ideal.span_singleton_pow, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.mem_span_singleton]
  obtain ⟨c, hc⟩ := (hZ _ _ n).mp (hL n)
  have h2 := congrArg (algebraMap ℤ_[p] R) hc
  rw [map_sub, map_natCast, map_mul, map_pow, map_natCast] at h2
  refine ⟨-(algebraMap ℤ_[p] R c + (seq n).1), ?_⟩
  linear_combination (-1 : R) * h2 - hrep n
