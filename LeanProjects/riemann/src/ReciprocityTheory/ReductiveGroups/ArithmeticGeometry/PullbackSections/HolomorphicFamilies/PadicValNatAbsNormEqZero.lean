import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.DiffAtOddSt
import Lemmata.MiscLemmasK.Imports
import Lemmata.FirstBlockLemmaL.Imports

noncomputable section

open NumberField UniqueFactorizationMonoid Pointwise

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf

section Gal

variable {E : Type} [Field E] [NumberField E]

theorem algebraMap_smul_oe (σ : E ≃ₐ[ℚ] E) (x : 𝓞 E) :
    algebraMap (𝓞 E) E (σ • x) = σ (algebraMap (𝓞 E) E x) := rfl

theorem mem_differentIdeal_iff (x : 𝓞 E) : x ∈ differentIdeal ℤ (𝓞 E) ↔
    algebraMap (𝓞 E) E x ∈ (1 / Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E) : Submodule (𝓞 E) E) := by
  rw [← coeSubmodule_differentIdeal ℤ ℚ, IsLocalization.mem_coeSubmodule]
  constructor
  · intro h
    exact ⟨x, h, rfl⟩
  · rintro ⟨y, hy, e⟩
    rwa [← (IsFractionRing.injective (𝓞 E) E) e]

theorem traceDual_smul (τ : E ≃ₐ[ℚ] E) {y : E} (hy : y ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E)) :
    τ y ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E) := by
  rw [Submodule.mem_traceDual] at hy ⊢
  intro a ha
  obtain ⟨o, rfl⟩ := Submodule.mem_one.mp ha
  have hb : τ.symm (algebraMap (𝓞 E) E o) ∈ (1 : Submodule (𝓞 E) E) :=
    Submodule.mem_one.mpr ⟨τ.symm • o, algebraMap_smul_oe τ.symm o⟩
  have key := hy _ hb
  rw [Algebra.traceForm_apply] at key ⊢
  rw [← Algebra.trace_eq_of_algEquiv τ, map_mul, AlgEquiv.apply_symm_apply] at key
  exact key

theorem smul_mem_differentIdeal (σ : E ≃ₐ[ℚ] E) {x : 𝓞 E} (hx : x ∈ differentIdeal ℤ (𝓞 E)) :
    σ • x ∈ differentIdeal ℤ (𝓞 E) := by
  rw [mem_differentIdeal_iff] at hx ⊢
  rw [Submodule.mem_div_iff_forall_mul_mem] at hx ⊢
  intro y hy
  have h1 := hx (σ.symm y) (traceDual_smul σ.symm hy)
  obtain ⟨o, ho⟩ := Submodule.mem_one.mp h1
  refine Submodule.mem_one.mpr ⟨σ • o, ?_⟩
  rw [algebraMap_smul_oe, ho, algebraMap_smul_oe, map_mul, AlgEquiv.apply_symm_apply]

theorem smul_differentIdeal (σ : E ≃ₐ[ℚ] E) : σ • differentIdeal ℤ (𝓞 E) = differentIdeal ℤ (𝓞 E) := by
  ext x
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  constructor
  · intro h
    simpa using smul_mem_differentIdeal σ h
  · intro h
    exact smul_mem_differentIdeal σ⁻¹ h

theorem smul_span_nat (σ : E ≃ₐ[ℚ] E) (ℓ : ℕ) :
    σ • Ideal.span {(ℓ : 𝓞 E)} = Ideal.span {(ℓ : 𝓞 E)} := by
  rw [Ideal.pointwise_smul_def, Ideal.map_span, Set.image_singleton, map_natCast]

theorem count_smul (σ : E ≃ₐ[ℚ] E) {P X : Ideal (𝓞 E)} (hP : P.IsPrime) (hP0 : P ≠ ⊥) (hQ : (σ • P).IsPrime)
    (hQ0 : σ • P ≠ ⊥) (hX : X ≠ ⊥) :
    (normalizedFactors (σ • X)).count (σ • P) = (normalizedFactors X).count P := by
  let f := MulDistribMulAction.toMulEquiv (Ideal (𝓞 E)) σ
  have hf : ∀ I : Ideal (𝓞 E), f I = σ • I := fun _ => rfl
  have hX' : (normalizedFactors X).prod = X :=
    (associated_iff_eq.mp (prod_normalizedFactors (by simpa using hX)))
  have hprime : ∀ p ∈ (normalizedFactors X).map f, Prime p := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
    exact (MulEquiv.prime_iff f).mpr (prime_of_normalized_factor q hq)
  have hmap : normalizedFactors (σ • X) = (normalizedFactors X).map f := by
    have h1 : ((normalizedFactors X).map f).prod = σ • X := by
      rw [← map_multiset_prod f, hX'] <;> rfl
    rw [← h1, normalizedFactors_prod_of_prime hprime]
  rw [hmap, ← hf]
  exact Multiset.count_map_eq_count' f _ f.injective P

end Gal

section Norm

variable {E : Type} [Field E] [NumberField E]

theorem padicValNat_multiset_prod (ℓ : ℕ) [Fact ℓ.Prime] (s : Multiset ℕ) (h : ∀ x ∈ s, x ≠ 0) :
    padicValNat ℓ s.prod = (s.map (padicValNat ℓ)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons b s ih =>
    have hb : b ≠ 0 := h b (Multiset.mem_cons_self b s)
    have hs : ∀ x ∈ s, x ≠ 0 := fun x hx => h x (Multiset.mem_cons_of_mem hx)
    have hp : s.prod ≠ 0 := Multiset.prod_ne_zero (fun h0 => hs 0 h0 rfl)
    rw [Multiset.prod_cons, padicValNat.mul hb hp, Multiset.map_cons, Multiset.sum_cons, ih hs]

theorem natCast_ne_zero_oe (ℓ : ℕ) [hℓ : Fact ℓ.Prime] : (ℓ : 𝓞 E) ≠ 0 := by
  intro h
  have h2 := congrArg (algebraMap (𝓞 E) E) h
  rw [map_natCast, map_zero, Nat.cast_eq_zero] at h2
  exact hℓ.out.ne_zero h2

theorem span_nat_ne_bot (ℓ : ℕ) [Fact ℓ.Prime] : Ideal.span {(ℓ : 𝓞 E)} ≠ ⊥ := by
  rw [Ne, Ideal.span_singleton_eq_bot]
  exact natCast_ne_zero_oe ℓ

theorem mem_factors_span (ℓ : ℕ) [Fact ℓ.Prime] {Q : Ideal (𝓞 E)} (hQ : Q.IsPrime) (hQ0 : Q ≠ ⊥)
    (hl : (ℓ : 𝓞 E) ∈ Q) : Q ∈ normalizedFactors (Ideal.span {(ℓ : 𝓞 E)}) := by
  rw [Ideal.mem_normalizedFactors_iff (span_nat_ne_bot ℓ)]
  exact ⟨hQ, (Ideal.span_singleton_le_iff_mem Q).mpr hl⟩

theorem of_mem_factors_span (ℓ : ℕ) [Fact ℓ.Prime] {Q : Ideal (𝓞 E)}
    (hQ : Q ∈ normalizedFactors (Ideal.span {(ℓ : 𝓞 E)})) : Q.IsPrime ∧ Q ≠ ⊥ ∧ (ℓ : 𝓞 E) ∈ Q := by
  have hQ' := (Ideal.mem_normalizedFactors_iff (span_nat_ne_bot ℓ)).mp hQ
  refine ⟨hQ'.1, ?_, (Ideal.span_singleton_le_iff_mem Q).mp hQ'.2⟩
  intro h0
  rw [h0, le_bot_iff] at hQ'
  exact span_nat_ne_bot ℓ hQ'.2

theorem padicValNat_absNorm_eq_sum (ℓ : ℕ) [Fact ℓ.Prime] {X : Ideal (𝓞 E)} (hX : X ≠ ⊥) :
    padicValNat ℓ (Ideal.absNorm X) = ∑ Q ∈ (normalizedFactors (Ideal.span {(ℓ : 𝓞 E)})).toFinset,
      (normalizedFactors X).count Q * padicValNat ℓ (Ideal.absNorm Q) := by
  classical
  have hv : ∀ Q : Ideal (𝓞 E), Q.IsPrime → Q ≠ ⊥ → (ℓ : 𝓞 E) ∉ Q →
      padicValNat ℓ (Ideal.absNorm Q) = 0 := by
    intro Q hQp hQ0 hlQ
    apply padicValNat.eq_zero_of_not_dvd
    intro hdvd
    haveI : Q.IsMaximal := hQp.isMaximal hQ0
    letI : Field (𝓞 E ⧸ Q) := Ideal.Quotient.field Q
    have hfin : Finite (𝓞 E ⧸ Q) := by
      apply Nat.finite_of_card_ne_zero
      rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ne, Ideal.absNorm_eq_zero_iff]
      exact hQ0
    haveI := Fintype.ofFinite (𝓞 E ⧸ Q)
    haveI := ringChar.charP (𝓞 E ⧸ Q)
    obtain ⟨n, hp, hcard⟩ := FiniteField.card (𝓞 E ⧸ Q) (ringChar (𝓞 E ⧸ Q))
    have hN : Ideal.absNorm Q = Fintype.card (𝓞 E ⧸ Q) := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
    rw [hN, hcard] at hdvd
    have heq : ℓ = ringChar (𝓞 E ⧸ Q) :=
      (Nat.prime_dvd_prime_iff_eq (Fact.out : ℓ.Prime) hp).mp ((Fact.out : ℓ.Prime).dvd_of_dvd_pow hdvd)
    apply hlQ
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, heq, ringChar.Nat.cast_ringChar]
  have hX' : (normalizedFactors X).prod = X :=
    associated_iff_eq.mp (prod_normalizedFactors (by simpa using hX))
  have hN : Ideal.absNorm X = ((normalizedFactors X).map Ideal.absNorm).prod := by
    conv_lhs => rw [← hX']
    exact map_multiset_prod Ideal.absNorm _
  have hnz : ∀ x ∈ (normalizedFactors X).map Ideal.absNorm, x ≠ 0 := by
    intro x hx
    obtain ⟨Q, hQ, rfl⟩ := Multiset.mem_map.mp hx
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact ne_zero_of_mem_normalizedFactors hQ
  rw [hN, padicValNat_multiset_prod ℓ _ hnz, Multiset.map_map, Finset.sum_multiset_map_count]
  simp only [smul_eq_mul, Function.comp_apply]
  set A := (normalizedFactors X).toFinset
  set B := (normalizedFactors (Ideal.span {(ℓ : 𝓞 E)})).toFinset
  calc ∑ Q ∈ A, (normalizedFactors X).count Q * padicValNat ℓ (Ideal.absNorm Q)
      = ∑ Q ∈ A ∪ B, (normalizedFactors X).count Q * padicValNat ℓ (Ideal.absNorm Q) := by
        apply Finset.sum_subset Finset.subset_union_left
        intro Q hQ hQA
        have hQB : Q ∈ B := by
          rcases Finset.mem_union.mp hQ with h | h
          · exact absurd h hQA
          · exact h
        have hc : (normalizedFactors X).count Q = 0 :=
          Multiset.count_eq_zero.mpr (fun h => hQA (Multiset.mem_toFinset.mpr h))
        rw [hc, zero_mul]
    _ = ∑ Q ∈ B, (normalizedFactors X).count Q * padicValNat ℓ (Ideal.absNorm Q) := by
        symm
        apply Finset.sum_subset Finset.subset_union_right
        intro Q hQ hQB
        have hQA : Q ∈ (normalizedFactors X) := by
          rcases Finset.mem_union.mp hQ with h | h
          · exact Multiset.mem_toFinset.mp h
          · exact absurd h hQB
        have hQp : Q.IsPrime := Ideal.isPrime_of_prime (prime_of_normalized_factor Q hQA)
        have hQ0 : Q ≠ ⊥ := ne_zero_of_mem_normalizedFactors hQA
        have hl : (ℓ : 𝓞 E) ∉ Q := fun h =>
          hQB (Multiset.mem_toFinset.mpr (mem_factors_span ℓ hQp hQ0 h))
        rw [hv Q hQp hQ0 hl, mul_zero]

theorem absNorm_span_nat (ℓ : ℕ) : Ideal.absNorm (Ideal.span {(ℓ : 𝓞 E)}) = ℓ ^ Module.finrank ℚ E := by
  rw [Ideal.absNorm_span_singleton, ← map_natCast (algebraMap ℤ (𝓞 E)), Algebra.norm_algebraMap,
    NumberField.RingOfIntegers.rank, Int.natAbs_pow, Int.natAbs_natCast]

end Norm

section Main

theorem liesOver_span (E : Type) [Field E] [NumberField E] (ℓ : ℕ) (hℓ : ℓ.Prime) {P : Ideal (𝓞 E)}
    (hP : P.IsPrime) (hl : (ℓ : 𝓞 E) ∈ P) : P.LiesOver (Ideal.span {(ℓ : ℤ)}) := by
  have hne : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ.ne_zero
  have hpr : (Ideal.span {(ℓ : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime hne).mpr (Nat.prime_iff_prime_int.mp hℓ)
  have hmax : (Ideal.span {(ℓ : ℤ)}).IsMaximal :=
    hpr.isMaximal (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hne)
  haveI := hP
  refine ⟨hmax.eq_of_le ?_ ?_⟩
  · exact (inferInstance : (P.under ℤ).IsPrime).ne_top
  · rw [Ideal.span_singleton_le_iff_mem, Ideal.under, Ideal.mem_comap]
    simpa using hl

theorem diffExp : DiffExpSt := by
  intro E _ _ _ ℓ a m hℓ hm hd P hP hl
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  classical
  have hP0 : P ≠ ⊥ := by
    rintro rfl
    exact natCast_ne_zero_oe (E := E) ℓ (Ideal.mem_bot.mp hl)
  have hnorm : Ideal.absNorm (differentIdeal ℤ (𝓞 E)) = (discr E).natAbs :=
    NumberField.absNorm_differentIdeal E (𝓞 E)
  have hD0 : differentIdeal ℤ (𝓞 E) ≠ ⊥ := by
    intro h
    rw [h, Ideal.absNorm_bot] at hnorm
    exact NumberField.discr_ne_zero E (Int.natAbs_eq_zero.mp hnorm.symm)
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero ℓ)
  have hA : padicValNat ℓ (Ideal.absNorm (differentIdeal ℤ (𝓞 E))) = a := by
    rw [hnorm, hd, padicValNat.mul (pow_ne_zero _ hℓ.ne_zero) hm0, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hm, add_zero]
  have hn : padicValNat ℓ (Ideal.absNorm (Ideal.span {(ℓ : 𝓞 E)})) = Module.finrank ℚ E := by
    rw [absNorm_span_nat, padicValNat.prime_pow]
  have htrans : ∀ Q ∈ (normalizedFactors (Ideal.span {(ℓ : 𝓞 E)})).toFinset,
      ∃ σ : E ≃ₐ[ℚ] E, σ • P = Q := by
    intro Q hQ
    obtain ⟨hQp, -, hlQ⟩ := of_mem_factors_span ℓ (Multiset.mem_toFinset.mp hQ)
    haveI := hP
    haveI := hQp
    have hPQ : P.under ℤ = Q.under ℤ := by
      rw [← (liesOver_span E ℓ hℓ hP hl).over, ← (liesOver_span E ℓ hℓ hQp hlQ).over]
    obtain ⟨σ, hσ⟩ := Algebra.IsInvariant.exists_smul_of_under_eq (A := ℤ) (B := 𝓞 E) (G := E ≃ₐ[ℚ] E) P Q hPQ
    exact ⟨σ, hσ.symm⟩
  have hN : ∀ (σ : E ≃ₐ[ℚ] E) (Q : Ideal (𝓞 E)), Ideal.absNorm (σ • Q) = Ideal.absNorm Q := by
    intro σ Q
    rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
    exact Nat.card_congr (Ideal.quotientEquiv Q (σ • Q) (MulSemiringAction.toRingEquiv _ _ σ)
      (by rw [Ideal.pointwise_smul_def]; rfl)).toEquiv.symm
  have hconst : ∀ X : Ideal (𝓞 E), X ≠ ⊥ → (∀ σ : E ≃ₐ[ℚ] E, σ • X = X) →
      padicValNat ℓ (Ideal.absNorm X) =
        (normalizedFactors (Ideal.span {(ℓ : 𝓞 E)})).toFinset.card *
          ((normalizedFactors X).count P * padicValNat ℓ (Ideal.absNorm P)) := by
    intro X hX hXσ
    rw [padicValNat_absNorm_eq_sum ℓ hX,
      Finset.sum_congr rfl (g := fun _ => (normalizedFactors X).count P * padicValNat ℓ (Ideal.absNorm P)),
      Finset.sum_const, smul_eq_mul]
    intro Q hQ
    obtain ⟨σ, rfl⟩ := htrans Q hQ
    obtain ⟨hQp, hQ0, -⟩ := of_mem_factors_span ℓ (Multiset.mem_toFinset.mp hQ)
    have hc := count_smul σ hP hP0 hQp hQ0 hX
    rw [hXσ σ] at hc
    rw [hN σ P, hc]
  have h1 := hconst _ hD0 (fun σ => smul_differentIdeal σ)
  have h2 := hconst _ (span_nat_ne_bot ℓ) (fun σ => smul_span_nat σ ℓ)
  rw [hA] at h1
  rw [hn] at h2
  rw [h1, h2]
  ring

theorem count_span_pos (E : Type) [Field E] [NumberField E] (ℓ : ℕ) (hℓ : ℓ.Prime) {P : Ideal (𝓞 E)}
    (hP : P.IsPrime) (hl : (ℓ : 𝓞 E) ∈ P) : 0 < (normalizedFactors (Ideal.span {(ℓ : 𝓞 E)})).count P := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hP0 : P ≠ ⊥ := by
    rintro rfl
    exact natCast_ne_zero_oe (E := E) ℓ (Ideal.mem_bot.mp hl)
  exact Multiset.count_pos.mpr (mem_factors_span ℓ hP hP0 hl)

end Main

end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf
