import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsGenericDimGe
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

namespace GenericDimGe

section Noetherian

variable {R : Type*} [CommRing R]

theorem map_mk_lt {p a b : Ideal R} (ha : p ≤ a) (hab : a < b) :
    a.map (Ideal.Quotient.mk p) < b.map (Ideal.Quotient.mk p) := by
  have key : ∀ c : Ideal R, p ≤ c →
      (c.map (Ideal.Quotient.mk p)).comap (Ideal.Quotient.mk p) = c := by
    intro c hc
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact sup_eq_left.mpr hc
  refine lt_of_le_of_ne (Ideal.map_mono hab.le) fun h => hab.ne ?_
  rw [← key a ha, ← key b (ha.trans hab.le), h]

theorem one_lt_height_map {p a b : Ideal R} [p.IsPrime] [a.IsPrime] [b.IsPrime] (hpa : p < a)
    (hab : a < b) : 1 < (b.map (Ideal.Quotient.mk p)).height := by
  have hk : ∀ c : Ideal R, p ≤ c → RingHom.ker (Ideal.Quotient.mk p) ≤ c := fun c hc => by
    rw [Ideal.mk_ker]; exact hc
  have := Ideal.map_isPrime_of_surjective (I := p) Ideal.Quotient.mk_surjective (hk p le_rfl)
  have := Ideal.map_isPrime_of_surjective (I := a) Ideal.Quotient.mk_surjective (hk a hpa.le)
  have := Ideal.map_isPrime_of_surjective (I := b) Ideal.Quotient.mk_surjective
    (hk b (hpa.trans hab).le)
  have h1 := Ideal.height_add_one_le_of_lt_of_isPrime (map_mk_lt le_rfl hpa)
  have h2 := Ideal.height_add_one_le_of_lt_of_isPrime (map_mk_lt hpa.le hab)
  have h3 : (1 : ℕ∞) ≤ (a.map (Ideal.Quotient.mk p)).height := le_trans le_add_self h1
  have h4 : (1 : ℕ∞) + 1 ≤ (b.map (Ideal.Quotient.mk p)).height :=
    le_trans (add_le_add h3 le_rfl) h2
  exact lt_of_lt_of_le (by norm_num) h4

theorem exists_isPrime_between_not_mem [IsNoetherianRing R] {p q r : Ideal R} [p.IsPrime]
    [q.IsPrime] [r.IsPrime] (hpq : p < q) (hqr : q < r) {x : R} (hx : x ∉ p) :
    ∃ q' : Ideal R, q'.IsPrime ∧ p < q' ∧ q' < r ∧ x ∉ q' := by
  classical
  by_contra H
  push Not at H
  have hM : (p ⊔ Ideal.span {x}).minimalPrimes.Finite :=
    Ideal.finite_minimalPrimes_of_isNoetherianRing R _
  let s : Finset (Ideal R) := insert p (hM.toFinset.filter (· < r))
  have hprime : ∀ t ∈ s, t.IsPrime := by
    intro t ht
    rcases Finset.mem_insert.1 ht with rfl | ht
    · infer_instance
    · exact (hM.mem_toFinset.1 (Finset.mem_filter.1 ht).1).isPrime
  have hlt : ∀ t ∈ s, t < r := by
    intro t ht
    rcases Finset.mem_insert.1 ht with rfl | ht
    · exact hpq.trans hqr
    · exact (Finset.mem_filter.1 ht).2
  have hnot : ¬ ((r : Set R) ⊆ ⋃ t ∈ (↑s : Set (Ideal R)), ((fun t : Ideal R => t) t : Set R)) := by
    intro h
    obtain ⟨t, ht, hrt⟩ :=
      (Ideal.subset_union_prime (f := fun t : Ideal R => t) p p
        (fun t ht _ _ => hprime t ht)).1 h
    exact (hlt t ht).not_ge hrt
  obtain ⟨y, hyr, hy⟩ := Set.not_subset.1 hnot
  simp only [Set.mem_iUnion, not_exists] at hy
  have hyp : y ∉ p := fun h => hy p (Finset.mem_coe.2 (Finset.mem_insert_self _ _)) h
  have hyt : ∀ t ∈ (p ⊔ Ideal.span {x}).minimalPrimes, t < r → y ∉ t := fun t ht htr h =>
    hy t (Finset.mem_coe.2 (Finset.mem_insert_of_mem
      (Finset.mem_filter.2 ⟨hM.mem_toFinset.2 ht, htr⟩))) h
  have hle : p ⊔ Ideal.span {y} ≤ r :=
    sup_le (hpq.trans hqr).le (by rwa [Ideal.span_le, Set.singleton_subset_iff])
  obtain ⟨t0, ht0, ht0r⟩ := Ideal.exists_minimalPrimes_le hle
  have : t0.IsPrime := ht0.isPrime
  have hKrull := Ideal.map_height_le_one_of_mem_minimalPrimes ht0
  have hyt0 : y ∈ t0 := ht0.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self y))
  have hpt0 : p < t0 :=
    lt_of_le_of_ne (le_sup_left.trans ht0.1.2) fun h => hyp (by rw [h]; exact hyt0)
  have ht0r' : t0 < r := by
    refine lt_of_le_of_ne ht0r fun h => ?_
    have h2 := one_lt_height_map hpq hqr
    rw [← h] at h2
    exact absurd hKrull (not_le.2 h2)
  have hxt0 : x ∈ t0 := H t0 inferInstance hpt0 ht0r'
  have hle' : p ⊔ Ideal.span {x} ≤ t0 :=
    sup_le (le_sup_left.trans ht0.1.2) (by rwa [Ideal.span_le, Set.singleton_subset_iff])
  obtain ⟨t', ht', ht't0⟩ := Ideal.exists_minimalPrimes_le hle'
  have : t'.IsPrime := ht'.isPrime
  have hxt' : x ∈ t' := ht'.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self x))
  have hpt' : p < t' :=
    lt_of_le_of_ne (le_sup_left.trans ht'.1.2) fun h => hx (by rw [h]; exact hxt')
  have ht'eq : t' = t0 := by
    by_contra hne
    exact absurd hKrull (not_le.2 (one_lt_height_map hpt' (lt_of_le_of_ne ht't0 hne)))
  exact hyt t' ht' (ht'eq ▸ ht0r') (ht'eq ▸ hyt0)

end Noetherian

theorem exists_lt_of_le_height {α : Type*} [Preorder α] {a : α} {n : ℕ}
    (h : ((n + 1 : ℕ) : ℕ∞) ≤ Order.height a) : ∃ b < a, (n : ℕ∞) ≤ Order.height b := by
  obtain ⟨p, hlast, hlen⟩ := Order.exists_series_of_le_height a h
  have hne : p.length ≠ 0 := by omega
  refine ⟨p.eraseLast.last, hlast ▸ p.eraseLast_last_rel_last hne, ?_⟩
  have := Order.length_le_height_last (p := p.eraseLast)
  simp only [RelSeries.eraseLast_length, hlen, Nat.add_sub_cancel] at this
  exact this

theorem comap_C_eq_bot {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {σ : Type*} {ϖ : O} (hϖ : Irreducible ϖ) (Q : Ideal (MvPolynomial σ O)) [Q.IsPrime]
    (h : (C ϖ : MvPolynomial σ O) ∉ Q) : Q.comap (C : O →+* MvPolynomial σ O) = ⊥ := by
  by_contra hne
  have : (Q.comap (C : O →+* MvPolynomial σ O)).IsMaximal :=
    Ideal.IsPrime.isMaximal inferInstance hne
  have hm := IsLocalRing.eq_maximalIdeal this
  apply h
  have : ϖ ∈ Q.comap (C : O →+* MvPolynomial σ O) := by
    rw [hm]; exact (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 hϖ.not_isUnit)
  exact this

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem proof : Statement.{u} := by
  intro O _ _ _ K _ _ ι _ P hP hPC
  classical
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  let M : Submonoid (MRing ι O) := (nonZeroDivisors O).map (C : O →+* MRing ι O)
  have : IsLocalization M (MRing ι (FractionRing O)) :=
    MvPolynomial.isLocalization (nonZeroDivisors O) (FractionRing O)
  rw [ringKrullDim_quotient, ringKrullDim_quotient]
  let Z := PrimeSpectrum.zeroLocus (R := MRing ι O) (P : Set (MRing ι O))
  let Z' := PrimeSpectrum.zeroLocus (R := MRing ι (FractionRing O))
    (genFib P : Set (MRing ι (FractionRing O)))
  let U := {q : Z // q.1.asIdeal.comap (C : O →+* MRing ι O) = ⊥}
  have ltZ : ∀ a b : Z, a < b ↔ a.1.asIdeal < b.1.asIdeal := fun a b =>
    Subtype.coe_lt_coe.symm.trans (PrimeSpectrum.asIdeal_lt_asIdeal _ _).symm
  have ltU : ∀ a b : U, a < b ↔ a.1.1.asIdeal < b.1.1.asIdeal := fun a b =>
    Subtype.coe_lt_coe.symm.trans (ltZ _ _)
  have memZ : ∀ x : PrimeSpectrum (MRing ι O), x ∈ Z ↔ P ≤ x.asIdeal := fun x =>
    PrimeSpectrum.mem_zeroLocus _ _
  let P0 : Z := ⟨⟨P, hP⟩, (memZ _).2 le_rfl⟩
  let PU : U := ⟨P0, hPC⟩

  have hstep : ∀ n : ℕ, ∀ r : Z, ((n + 1 : ℕ) : ℕ∞) ≤ Order.height r →
      ∃ q : U, q.1.1.asIdeal < r.1.asIdeal ∧ (n : ℕ∞) ≤ Order.height q := by
    intro n
    induction n with
    | zero =>
      intro r hr
      obtain ⟨r0, hr0, -⟩ := exists_lt_of_le_height hr
      exact ⟨PU, lt_of_le_of_lt ((memZ _).1 r0.2) ((ltZ _ _).1 hr0), by simp⟩
    | succ n ih =>
      intro r hr
      obtain ⟨r', hr'r, hr'⟩ := exists_lt_of_le_height hr
      obtain ⟨q, hqr', hq⟩ := ih r' hr'
      have hx : (C ϖ : MRing ι O) ∉ q.1.1.asIdeal := fun h => hϖ.ne_zero (by
        have : ϖ ∈ q.1.1.asIdeal.comap (C : O →+* MRing ι O) := h
        rw [q.2] at this
        exact (Submodule.mem_bot _).1 this)
      obtain ⟨q', hq'p, hqq', hq'r, hq'x⟩ :=
        exists_isPrime_between_not_mem hqr' ((ltZ _ _).1 hr'r) hx
      let qZ : Z := ⟨⟨q', hq'p⟩, (memZ _).2 (((memZ _).1 q.1.2).trans hqq'.le)⟩
      let qU : U := ⟨qZ, comap_C_eq_bot hϖ q' hq'x⟩
      refine ⟨qU, hq'r, ?_⟩
      have hlt : q < qU := (ltU _ _).2 hqq'
      calc ((n + 1 : ℕ) : ℕ∞) = (n : ℕ∞) + 1 := by push_cast; rfl
        _ ≤ Order.height q + 1 := add_le_add hq le_rfl
        _ ≤ Order.height qU := Order.height_add_one_le hlt
  have hbound : ∀ r : Z, Order.height r ≤ (⨆ q : U, Order.height q) + 1 := by
    intro r
    refine ENat.forall_natCast_le_iff_le.1 fun m hm => ?_
    cases m with
    | zero => simp
    | succ m =>
      obtain ⟨q, -, hq⟩ := hstep m r hm
      push_cast
      exact add_le_add (hq.trans (le_iSup (fun q : U => Order.height q) q)) le_rfl

  have hdisj : ∀ q : U, Disjoint (M : Set (MRing ι O)) (q.1.1.asIdeal : Set (MRing ι O)) := by
    intro q
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨a, ha, rfl⟩ hmem
    have : a ∈ q.1.1.asIdeal.comap (C : O →+* MRing ι O) := hmem
    rw [q.2] at this
    exact nonZeroDivisors.ne_zero ha ((Submodule.mem_bot _).1 this)
  let Φ : U → Z' := fun q =>
    ⟨⟨q.1.1.asIdeal.map (algebraMap (MRing ι O) (MRing ι (FractionRing O))),
      IsLocalization.isPrime_of_isPrime_disjoint M _ _ q.1.1.2 (hdisj q)⟩, by
      rw [PrimeSpectrum.mem_zeroLocus]
      exact Ideal.map_mono ((memZ _).1 q.1.2)⟩
  have hΦ : StrictMono Φ := by
    intro a b hab
    rw [ltU] at hab
    refine Subtype.coe_lt_coe.1 ((PrimeSpectrum.asIdeal_lt_asIdeal _ _).1 ?_)
    refine lt_of_le_of_ne (Ideal.map_mono hab.le) fun h => hab.ne ?_
    have ha := IsLocalization.under_map_of_isPrime_disjoint M (MRing ι (FractionRing O))
      a.1.1.2 (hdisj a)
    have hb := IsLocalization.under_map_of_isPrime_disjoint M (MRing ι (FractionRing O))
      b.1.1.2 (hdisj b)
    rw [← ha, ← hb]
    exact congrArg (Ideal.comap _) h
  have : Nonempty Z := ⟨P0⟩
  have : Nonempty U := ⟨PU⟩
  calc Order.krullDim Z = ((⨆ r : Z, Order.height r : ℕ∞) : WithBot ℕ∞) :=
        Order.krullDim_eq_iSup_height_of_nonempty
    _ ≤ (((⨆ q : U, Order.height q) + 1 : ℕ∞) : WithBot ℕ∞) :=
        WithBot.coe_le_coe.2 (iSup_le hbound)
    _ = Order.krullDim U + 1 := by
        rw [Order.krullDim_eq_iSup_height_of_nonempty (α := U)]; rfl
    _ ≤ Order.krullDim Z' + 1 := add_le_add (Order.krullDim_le_of_strictMono Φ hΦ) le_rfl

end GenericDimGe

end

end GroundTheory.Heights₂.Heights.NumbersDVR
