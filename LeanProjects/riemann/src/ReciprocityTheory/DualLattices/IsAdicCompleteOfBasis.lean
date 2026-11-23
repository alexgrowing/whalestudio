import Mathlib

noncomputable section

open Polynomial IsLocalRing

namespace ReciprocityTheory.PGsh.Up.FrobeniusGroupField

variable {p : ℕ} [hp : Fact p.Prime]

theorem smul_top_self (k : ℕ) :
    ((maximalIdeal ℤ_[p]) ^ k • ⊤ : Submodule ℤ_[p] ℤ_[p]) = (maximalIdeal ℤ_[p]) ^ k := by
  rw [smul_eq_mul, Ideal.mul_top]

theorem mem_pow_smul_top_iff {M : Type} [AddCommGroup M] [Module ℤ_[p] M] {ι : Type} [Fintype ι]
    (b : Module.Basis ι ℤ_[p] M) (k : ℕ) (x : M) :
    x ∈ ((maximalIdeal ℤ_[p]) ^ k • ⊤ : Submodule ℤ_[p] M) ↔
      ∀ i, b.repr x i ∈ (maximalIdeal ℤ_[p]) ^ k := by
  constructor
  · intro hx i
    have hle : ((maximalIdeal ℤ_[p]) ^ k • ⊤ : Submodule ℤ_[p] M) ≤
        Submodule.comap (b.coord i) ((maximalIdeal ℤ_[p]) ^ k) :=
      Submodule.smul_le.2 fun r hr m _ => by
        rw [Submodule.mem_comap, map_smul, smul_eq_mul]
        exact Ideal.mul_mem_right _ _ hr
    exact hle hx
  · intro h
    rw [← b.sum_repr x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (h i) Submodule.mem_top

theorem isPrecomplete_of_basis {M : Type} [AddCommGroup M] [Module ℤ_[p] M] {ι : Type} [Fintype ι]
    (b : Module.Basis ι ℤ_[p] M) : IsPrecomplete (maximalIdeal ℤ_[p]) M := by
  rw [isPrecomplete_iff]
  intro F hF
  have hP := (inferInstance : IsPrecomplete (maximalIdeal ℤ_[p]) ℤ_[p])
  rw [isPrecomplete_iff] at hP
  have hc : ∀ i, ∃ L : ℤ_[p], ∀ k, b.repr (F k) i ≡ L
      [SMOD ((maximalIdeal ℤ_[p]) ^ k • ⊤ : Submodule ℤ_[p] ℤ_[p])] := by
    intro i
    refine hP (fun k => b.repr (F k) i) fun {m n} hmn => ?_
    have := hF hmn
    rw [SModEq.sub_mem, mem_pow_smul_top_iff b] at this
    rw [SModEq.sub_mem, smul_top_self]
    simpa using this i
  choose L hL using hc
  refine ⟨∑ i, L i • b i, fun k => ?_⟩
  rw [SModEq.sub_mem, mem_pow_smul_top_iff b]
  intro i
  have := hL i k
  rw [SModEq.sub_mem, smul_top_self] at this
  have hr : b.repr (∑ j, L j • b j) i = L i := by
    have h := congrFun (b.equivFun.apply_symm_apply L) i
    rwa [Module.Basis.equivFun_symm_apply, Module.Basis.equivFun_apply] at h
  rw [map_sub, Finsupp.sub_apply, hr]
  exact this

theorem span_p_eq (S : Type) [CommRing S] [Algebra ℤ_[p] S] :
    (maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] S) = Ideal.span {(p : S)} := by
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton, map_natCast]

theorem isAdicComplete_of_basis (S : Type) [CommRing S] [Algebra ℤ_[p] S] {ι : Type} [Fintype ι]
    (b : Module.Basis ι ℤ_[p] S) : IsAdicComplete (Ideal.span {(p : S)}) S := by
  have : Module.Finite ℤ_[p] S := Module.Finite.of_basis b
  have hH : IsHausdorff (maximalIdeal ℤ_[p]) S := inferInstance
  have hP : IsPrecomplete (maximalIdeal ℤ_[p]) S := isPrecomplete_of_basis b
  rw [← span_p_eq S]
  exact { toIsHausdorff := IsHausdorff.map_algebraMap_iff.2 hH
          toIsPrecomplete := IsPrecomplete.map_algebraMap_iff.2 hP }

theorem hensel (f : ℤ_[p][X]) (hf : f.Monic) {m : ℕ} (hm0 : 0 < m) (hmp : ¬ p ∣ m) (Q0 : ℤ_[p][X])
    (h0 : ∃ K : ℤ_[p][X], AdjoinRoot.mk f (Q0 ^ m - 1) = (p : AdjoinRoot f) * AdjoinRoot.mk f K) :
    ∃ Q K : ℤ_[p][X], f ∣ Q ^ m - 1 ∧
      AdjoinRoot.mk f (Q - Q0) = (p : AdjoinRoot f) * AdjoinRoot.mk f K := by
  let S := AdjoinRoot f
  let J : Ideal S := Ideal.span {(p : S)}
  have : IsAdicComplete J S := isAdicComplete_of_basis S (AdjoinRoot.powerBasis' hf).basis
  have hHen : HenselianRing S J := inferInstance
  obtain ⟨K0, hK0⟩ := h0
  set a0 : S := AdjoinRoot.mk f Q0
  have ha0 : a0 ^ m - 1 ∈ J := by
    have : a0 ^ m - 1 = AdjoinRoot.mk f (Q0 ^ m - 1) := by simp [a0]
    rw [this, hK0]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  have hmon : (X ^ m - C (1 : S)).Monic := monic_X_pow_sub_C _ hm0.ne'
  have hev : (X ^ m - C (1 : S)).eval a0 ∈ J := by simpa using ha0
  have hu0 : IsUnit (Ideal.Quotient.mk J a0) := by
    have h1 : (Ideal.Quotient.mk J a0) ^ m = 1 := by
      rw [← map_pow, ← sub_eq_zero, ← map_one (Ideal.Quotient.mk J), ← map_sub]
      exact Ideal.Quotient.eq_zero_iff_mem.2 ha0
    exact IsUnit.of_pow_eq_one h1 hm0.ne'
  have hum : IsUnit (m : S ⧸ J) := by
    have hcop : Nat.Coprime m p :=
      Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hmp)
    have hg := Nat.gcd_eq_gcd_ab m p
    rw [hcop, Nat.cast_one] at hg
    have hp0 : (p : S ⧸ J) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk J)]
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
    refine IsUnit.of_mul_eq_one ((Nat.gcdA m p : ℤ) : S ⧸ J) ?_
    have := congrArg (fun z : ℤ => (z : S ⧸ J)) hg
    simp only [Int.cast_one, Int.cast_add, Int.cast_mul, Int.cast_natCast, hp0, zero_mul,
      add_zero] at this
    exact this.symm
  have hder : IsUnit (Ideal.Quotient.mk J ((X ^ m - C (1 : S)).derivative.eval a0)) := by
    simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, eval_mul, eval_natCast,
      eval_pow, eval_X, map_mul, map_pow, map_natCast]
    exact hum.mul (hu0.pow _)
  obtain ⟨a, ha, haJ⟩ := hHen.is_henselian _ hmon a0 hev hder
  obtain ⟨Q, rfl⟩ := AdjoinRoot.mk_surjective a
  refine ⟨Q, ?_⟩
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 haJ
  obtain ⟨K, rfl⟩ := AdjoinRoot.mk_surjective s
  refine ⟨K, ?_, ?_⟩
  · rw [← AdjoinRoot.mk_eq_zero, map_sub, map_pow, map_one]
    simpa [IsRoot, sub_eq_zero] using ha
  · rw [map_sub, ← hs, mul_comm]

theorem finite_quot (f : ℤ_[p][X]) (hf : f.Monic) :
    Finite (AdjoinRoot f ⧸ Ideal.span {(p : AdjoinRoot f)}) := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  let S := AdjoinRoot f
  let J : Ideal S := Ideal.span {(p : S)}
  let b := (AdjoinRoot.powerBasis' hf).basis
  let Φ : (Fin (AdjoinRoot.powerBasis' hf).dim → ZMod p) → S ⧸ J := fun c =>
    Ideal.Quotient.mk J (∑ i, (((c i).val : ℕ) : ℤ_[p]) • b i)
  refine Finite.of_surjective Φ fun y => ?_
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨fun i => PadicInt.toZMod (b.repr s i), ?_⟩
  simp only [Φ]
  rw [Ideal.Quotient.eq]
  have key : (∑ i, (((PadicInt.toZMod (b.repr s i)).val : ℕ) : ℤ_[p]) • b i) - s =
      ∑ i, ((((PadicInt.toZMod (b.repr s i)).val : ℕ) : ℤ_[p]) - b.repr s i) • b i := by
    simp only [sub_smul, Finset.sum_sub_distrib, b.sum_repr]
  rw [key]
  refine Ideal.sum_mem _ fun i _ => ?_
  have hz := PadicInt.toZMod_spec (b.repr s i)
  rw [ZMod.cast_eq_val, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at hz
  obtain ⟨w, hw⟩ := hz
  have : (((PadicInt.toZMod (b.repr s i)).val : ℕ) : ℤ_[p]) - b.repr s i = -(w * p) := by
    rw [hw]; ring
  rw [this, neg_smul, mul_comm, mul_smul, Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
  exact J.neg_mem (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))

theorem exists_pow_idem {S : Type} [Monoid S] [Finite S] (x : S) :
    ∃ M : ℕ, 0 < M ∧ x ^ (2 * M) = x ^ M := by
  obtain ⟨a, b, hab, he⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => x ^ n)
  wlog h : a < b generalizing a b
  · exact this b a hab.symm he.symm (lt_of_le_of_ne (not_lt.1 h) hab.symm)
  set d := b - a with hd
  have hd0 : 0 < d := by omega
  have hstep : ∀ n, a ≤ n → x ^ (n + d) = x ^ n := by
    intro n hn
    have : n + d = (n - a) + b := by omega
    rw [this, pow_add, ← he, ← pow_add]; congr 1; omega
  have hk : ∀ k n, a ≤ n → x ^ (n + k * d) = x ^ n := by
    intro k
    induction k with
    | zero => intro n _; simp
    | succ k ih =>
      intro n hn
      rw [show n + (k + 1) * d = (n + k * d) + d by ring, hstep _ (by omega), ih n hn]
  refine ⟨d * (a + 1), Nat.mul_pos hd0 (Nat.succ_pos a), ?_⟩
  rw [show 2 * (d * (a + 1)) = d * (a + 1) + (a + 1) * d by ring]
  exact hk _ _ (by nlinarith)

end ReciprocityTheory.PGsh.Up.FrobeniusGroupField
