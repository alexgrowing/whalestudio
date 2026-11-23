import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.MemDivSuppOfDivCycleNeZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.SwapLoc

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.AI.I1

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {F : Type*} [Field F]

theorem not_lt_lt_of_mem_minimalPrimes {V W W' : Ideal (MRingOver F ι)} [V.IsPrime] [W'.IsPrime]
    {x : MRingOver F ι} (hW : W ∈ (V ⊔ Ideal.span {x}).minimalPrimes) (hVW' : V < W')
    (hW'W : W' < W) : False := by
  have hWp : W.IsPrime := hW.isPrime
  have h1 := Ideal.map_height_le_one_of_mem_minimalPrimes hW
  set q := Ideal.Quotient.mk V
  have hker : RingHom.ker q = V := Ideal.mk_ker
  have hW'm : (W'.map q).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [hker]; exact hVW'.le)
  have hWm : (W.map q).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
      (by rw [hker]; exact hVW'.le.trans hW'W.le)
  have hlt : W'.map q < W.map q := by
    refine lt_of_le_of_ne (Ideal.map_mono hW'W.le) fun he => hW'W.ne ?_
    have := congrArg (Ideal.comap q) he
    rwa [Ideal.comap_map_of_surjective' q Ideal.Quotient.mk_surjective,
      Ideal.comap_map_of_surjective' q Ideal.Quotient.mk_surjective, hker,
      sup_eq_left.mpr hVW'.le, sup_eq_left.mpr (hVW'.le.trans hW'W.le)] at this
  have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  have h0 : (W'.map q).height = 0 := by
    have h3 := h2.trans h1
    generalize (W'.map q).height = a at h3
    cases a with
    | top => simp at h3
    | coe a => norm_cast at h3 ⊢; omega
  haveI : IsDomain (MRingOver F ι ⧸ V) := Ideal.Quotient.isDomain V
  rw [Ideal.height_eq_zero_iff_eq_bot] at h0
  apply hVW'.ne
  apply le_antisymm hVW'.le
  intro y hy
  have : q y ∈ W'.map q := Ideal.mem_map_of_mem q hy
  rw [h0, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at this
  exact this

theorem not_mem_of_mem_divSupp_swap {V W : Ideal (MRingOver F ι)} {n : ℕ} {f t : MRingOver F ι}
    {α β : K → ℕ} (hV : IsProjVarF V (n + 1)) (hf : IsMultiHomog f α) (ht : IsMultiHomog t β)
    (hfV : f ∉ V) (htV : t ∉ V) (hft : ∀ W ∈ divSupp V f, t ∉ W) (hW : W ∈ divSupp V t) :
    f ∉ W := by
  intro hfW
  haveI hVp : V.IsPrime := hV.1.1
  have hWp : W.IsPrime := hW.1.isPrime
  have hle : V ⊔ Ideal.span {f} ≤ W :=
    sup_le (le_sup_left.trans hW.1.1.2) (Ideal.span_le.mpr (by simpa using hfW))
  obtain ⟨W', hW', hW'W⟩ := Ideal.exists_minimalPrimes_le hle
  haveI : W'.IsPrime := hW'.isPrime
  have hVW' : V < W' := lt_of_le_of_ne (le_sup_left.trans hW'.1.2) fun he =>
    hfV (he ▸ hW'.1.2 (le_sup_right (a := V) (Ideal.subset_span rfl)))
  rcases hW'W.lt_or_eq with hlt | heq
  · exact not_lt_lt_of_mem_minimalPrimes hW.1 hVW' hlt
  · subst heq
    exact hft W' ⟨hW', hW.2⟩ (hW.1.1.2 (le_sup_right (a := V) (Ideal.subset_span rfl)))

open SwapLoc

namespace DivisorCycleSwap

theorem not_lt_of_dim_eq {R : Type*} [CommRing R] {P Q : Ideal R} [hP : P.IsPrime] [Q.IsPrime]
    (hlt : P < Q) {d : ℕ} (hPd : ringKrullDim (R ⧸ P) = (d : WithBot ℕ∞))
    (hQd : ringKrullDim (R ⧸ Q) = (d : WithBot ℕ∞)) : False := by
  obtain ⟨z, hzQ, hzP⟩ := SetLike.exists_of_lt hlt
  have hz : Ideal.Quotient.mk P z ∈ nonZeroDivisors (R ⧸ P) :=
    mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
  have h1 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hz
  have hle : Ideal.span {Ideal.Quotient.mk P z} ≤ Q.map (Ideal.Quotient.mk P) := by
    rw [Ideal.span_le, Set.singleton_subset_iff]; exact Ideal.mem_map_of_mem _ hzQ
  let e : (R ⧸ P) ⧸ Q.map (Ideal.Quotient.mk P) ≃+* R ⧸ Q :=
    (DoubleQuot.quotQuotEquivQuotSup P Q).trans (Ideal.quotEquivOfEq (sup_eq_right.mpr hlt.le))
  have h2 : ringKrullDim (R ⧸ Q) ≤ ringKrullDim ((R ⧸ P) ⧸ Ideal.span {Ideal.Quotient.mk P z}) :=
    ringKrullDim_le_of_surjective ((e : _ →+* R ⧸ Q).comp (Ideal.Quotient.factor hle))
      (e.surjective.comp (Ideal.Quotient.factor_surjective hle))
  rw [hPd] at h1
  rw [hQd] at h2
  have h3 : (d : WithBot ℕ∞) + 1 ≤ (d : WithBot ℕ∞) := le_trans (by gcongr) h1
  have h4 : ((d + 1 : ℕ) : WithBot ℕ∞) ≤ (d : WithBot ℕ∞) := by exact_mod_cast h3
  have h5 : d + 1 ≤ d := by exact_mod_cast h4
  omega

theorem isRelevant_of_le {Y Z : Ideal (MRingOver F ι)} (hZ : IsRelevant Z) (hY : Y ≤ Z) :
    IsRelevant Y := fun k => by
  obtain ⟨i, hi⟩ := hZ k
  exact ⟨i, fun h => hi (hY h)⟩

theorem divCycle_apply_of_mem {V W : Ideal (MRingOver F ι)} {f : MRingOver F ι}
    (hW : W ∈ divSupp V f) : divCycle V f W = multAt (V ⊔ Ideal.span {f}) W := by
  simp [divCycle, Finsupp.ofSupportFinite_coe, hW]

theorem divCycle_apply_of_not_mem {V W : Ideal (MRingOver F ι)} {f : MRingOver F ι}
    (hW : W ∉ divSupp V f) : divCycle V f W = 0 := by
  simp [divCycle, Finsupp.ofSupportFinite_coe, hW]

theorem ratDiv_one_eq (X : Ideal (MRingOver F ι)) (g : MRingOver F ι) :
    ratDiv X g 1 = Finsupp.mapRange (fun n : ℕ => (n : ℤ)) Nat.cast_zero (divCycle X g) := by
  simp [ratDiv, divCycle_one]

theorem sum_ratDiv_eq (V Z : Ideal (MRingOver F ι)) (f t : MRingOver F ι) :
    (ratDiv V f 1).sum (fun W m => m * ratDiv W t 1 Z) =
      ((∑ W ∈ (divSupp_finite V f).toFinset, divCycle V f W * divCycle W t Z : ℕ) : ℤ) := by
  classical
  have hs : (divCycle V f).support ⊆ (divSupp_finite V f).toFinset := by
    intro W hW
    rw [Finsupp.mem_support_iff] at hW
    exact (divSupp_finite V f).mem_toFinset.mpr (mem_divSupp_of_divCycle_ne_zero hW)
  rw [ratDiv_one_eq, Finsupp.sum_mapRange_index (fun _ => by simp),
    Finsupp.sum_of_support_subset _ hs _ (fun _ _ => by simp)]
  push_cast
  refine Finset.sum_congr rfl fun W _ => ?_
  rw [ratDiv_one_eq, Finsupp.mapRange_apply]

theorem cast_multAt {J W : Ideal (MRingOver F ι)} [hW : W.IsPrime] (hJ : W ∈ J.minimalPrimes) :
    ((multAt J W : ℕ) : ℕ∞) = lenAt J W := by
  rw [multAt_eq J W hW, ENat.coe_toNat (locLen_ne_top hJ), lenAt_eq]
  rfl

theorem mem_minimalPrimes_sup_of_le {V W Z : Ideal (MRingOver F ι)} {f t : MRingOver F ι}
    (hZ : Z ∈ (V ⊔ Ideal.span {f} ⊔ Ideal.span {t}).minimalPrimes)
    (hW : W ∈ (V ⊔ Ideal.span {f}).minimalPrimes) (hWZ : W ≤ Z) :
    Z ∈ (W ⊔ Ideal.span {t}).minimalPrimes :=
  ⟨⟨hZ.1.1, sup_le hWZ (le_sup_right.trans hZ.1.2)⟩, fun _ ⟨hQ, hQle⟩ hQZ =>
    hZ.2 ⟨hQ, sup_le (hW.1.2.trans (le_sup_left.trans hQle)) (le_sup_right.trans hQle)⟩ hQZ⟩

theorem mem_minimalPrimes_of_mem_divSupp_divSupp {V W Z : Ideal (MRingOver F ι)} {n : ℕ}
    {f t : MRingOver F ι} {α β : K → ℕ} (hV : IsProjVarF V (n + 2)) (hf : IsMultiHomog f α)
    (ht : IsMultiHomog t β) (hfV : f ∉ V) (hft : ∀ W ∈ divSupp V f, t ∉ W)
    (hW : W ∈ divSupp V f) (hZ : Z ∈ divSupp W t) :
    Z ∈ (V ⊔ Ideal.span {f} ⊔ Ideal.span {t}).minimalPrimes := by
  have hWd := isProjVarF_of_mem_divSupp (n := n + 1) hV hf hfV hW
  have hZd := isProjVarF_of_mem_divSupp hWd ht (hft W hW) hZ
  have hWZ : W ≤ Z := le_sup_left.trans hZ.1.1.2
  have hle : V ⊔ Ideal.span {f} ⊔ Ideal.span {t} ≤ Z :=
    sup_le (hW.1.1.2.trans hWZ) (le_sup_right.trans hZ.1.1.2)
  refine ⟨⟨hZ.1.1.1, hle⟩, fun Q ⟨hQ, hQle⟩ hQZ => ?_⟩
  by_contra hZQ
  have hlt : Q < Z := lt_of_le_of_ne hQZ fun e => hZQ (e ▸ le_rfl)
  obtain ⟨W', hW', hW'Q⟩ := Ideal.exists_minimalPrimes_le (le_sup_left.trans hQle)
  have hW'd : W' ∈ divSupp V f := ⟨hW', isRelevant_of_le hZ.2 (hW'Q.trans hQZ)⟩
  obtain ⟨Q', hQ', hQ'Q⟩ :=
    Ideal.exists_minimalPrimes_le (sup_le hW'Q (le_sup_right.trans hQle) :
      W' ⊔ Ideal.span {t} ≤ Q)
  have hQ'd : Q' ∈ divSupp W' t := ⟨hQ', isRelevant_of_le hZ.2 (hQ'Q.trans hQZ)⟩
  have h1 := isProjVarF_of_mem_divSupp (n := n + 1) hV hf hfV hW'd
  have h2 := isProjVarF_of_mem_divSupp h1 ht (hft W' hW'd) hQ'd
  haveI := hQ'.1.1
  haveI := hZ.1.1.1
  exact not_lt_of_dim_eq (hQ'Q.trans_lt hlt) h2.2 hZd.2

theorem sum_eq_zero_of_not {V Z : Ideal (MRingOver F ι)} {n : ℕ} {f t : MRingOver F ι}
    {α β : K → ℕ} (hV : IsProjVarF V (n + 2)) (hf : IsMultiHomog f α) (ht : IsMultiHomog t β)
    (hfV : f ∉ V) (hft : ∀ W ∈ divSupp V f, t ∉ W)
    (hZ : ¬ (IsRelevant Z ∧ Z ∈ (V ⊔ Ideal.span {f} ⊔ Ideal.span {t}).minimalPrimes)) :
    ∑ W ∈ (divSupp_finite V f).toFinset, divCycle V f W * divCycle W t Z = 0 := by
  refine Finset.sum_eq_zero fun W hW => ?_
  rw [Set.Finite.mem_toFinset] at hW
  by_contra hne
  have hZ' := mem_divSupp_of_divCycle_ne_zero (right_ne_zero_of_mul hne)
  exact hZ ⟨hZ'.2, mem_minimalPrimes_of_mem_divSupp_divSupp hV hf ht hfV hft hW hZ'⟩

theorem sum_eq_finsum {V Z : Ideal (MRingOver F ι)} [V.IsPrime] [hZp : Z.IsPrime]
    [(Z.map (Ideal.Quotient.mk V)).IsPrime] {f t : MRingOver F ι} (hZr : IsRelevant Z)
    (hZ : Z ∈ (V ⊔ Ideal.span {f} ⊔ Ideal.span {t}).minimalPrimes) (hfV : f ∉ V) :
    ((∑ W ∈ (divSupp_finite V f).toFinset, divCycle V f W * divCycle W t Z : ℕ) : ℕ∞) =
      ∑ᶠ (p : PrimeSpectrum (Localization.AtPrime (Z.map (Ideal.Quotient.mk V))))
        (_ : p.asIdeal.height = 1 ∧
          algebraMap (MRingOver F ι) (Localization.AtPrime (Z.map (Ideal.Quotient.mk V))) f ∈
            p.asIdeal),
        ordLoc p (algebraMap (MRingOver F ι) _ f) * ordMod p (algebraMap (MRingOver F ι) _ t) := by
  classical
  have hVZ : V ≤ Z := le_sup_left.trans (le_sup_left.trans hZ.1.2)
  have h := isLocData_atPrime_quot V Z hVZ
  have hex : ∀ Q : Ideal (MRingOver F ι), Q.IsPrime → V ≤ Q → Q ≤ Z →
      ∃ p : Ideal (Localization.AtPrime (Z.map (Ideal.Quotient.mk V))), p.IsPrime ∧
        p.comap (algebraMap (MRingOver F ι) _) = Q :=
    fun Q hQ hVQ hQZ => exists_prime_comap_atPrime_quot V Z Q hQ hVQ hQZ
  have hterm : ∀ W ∈ (divSupp_finite V f).toFinset, divCycle V f W * divCycle W t Z =
      if W ≤ Z then multAt (V ⊔ Ideal.span {f}) W * multAt (W ⊔ Ideal.span {t}) Z else 0 := by
    intro W hW
    rw [Set.Finite.mem_toFinset] at hW
    rw [divCycle_apply_of_mem hW]
    split_ifs with hWZ
    · rw [divCycle_apply_of_mem ⟨mem_minimalPrimes_sup_of_le hZ hW.1 hWZ, hZr⟩]
    · rw [divCycle_apply_of_not_mem (fun h' => hWZ (le_sup_left.trans h'.1.1.2)), mul_zero]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter]
  push_cast
  rw [← finsum_mem_coe_finset]
  symm
  refine finsum_mem_eq_of_bijOn (fun p => p.asIdeal.comap (algebraMap (MRingOver F ι) _))
    ⟨?_, ?_, ?_⟩ ?_
  · intro p hp
    have hm := (h.height_eq_one_iff hVZ hex hfV p.asIdeal).mp hp
    have hle := h.comap_le p.asIdeal
    simp only [Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    exact ⟨⟨hm, isRelevant_of_le hZr hle⟩, hle⟩
  · intro p _ p' _ e
    exact PrimeSpectrum.ext (h.eq_of_comap_eq e)
  · intro W hW
    simp only [Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hW
    obtain ⟨p, hp, hpW⟩ := hex W hW.1.1.1.1 (le_sup_left.trans hW.1.1.1.2) hW.2
    haveI := hp
    exact ⟨⟨p, hp⟩, (h.height_eq_one_iff hVZ hex hfV p).mpr (hpW ▸ hW.1.1), hpW⟩
  · intro p hp
    have hm := (h.height_eq_one_iff hVZ hex hfV p.asIdeal).mp hp
    have hle := h.comap_le p.asIdeal
    rw [cast_multAt hm, cast_multAt (mem_minimalPrimes_sup_of_le hZ hm hle), lenAt_eq, lenAt_eq,
      (h.atPrime p.asIdeal).length_eq f, (h.quot p.asIdeal).length_eq t, ordLoc, ordMod,
      ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply (MRingOver F ι) (Localization.AtPrime (Z.map (Ideal.Quotient.mk V)))
        (Localization.AtPrime (Z.map (Ideal.Quotient.mk V)) ⧸ p.asIdeal),
      Ideal.Quotient.algebraMap_eq]

end DivisorCycleSwap

open DivisorCycleSwap

theorem swap_coeff {V Z : Ideal (MRingOver F ι)} {n : ℕ} {f t : MRingOver F ι} {α β : K → ℕ}
    (hV : IsProjVarF V (n + 2)) (hf : IsMultiHomog f α) (ht : IsMultiHomog t β) (hfV : f ∉ V)
    (htV : t ∉ V) (hft : ∀ W ∈ divSupp V f, t ∉ W) :
    (ratDiv V f 1).sum (fun W m => m * ratDiv W t 1 Z) =
      (ratDiv V t 1).sum (fun W m => m * ratDiv W f 1 Z) := by
  classical
  haveI : V.IsPrime := hV.1.1
  have hft' : ∀ W ∈ divSupp V t, f ∉ W := fun W hW =>
    not_mem_of_mem_divSupp_swap (n := n + 1) hV hf ht hfV htV hft hW
  rw [sum_ratDiv_eq, sum_ratDiv_eq, Nat.cast_inj]
  by_cases hZ : IsRelevant Z ∧ Z ∈ (V ⊔ Ideal.span {f} ⊔ Ideal.span {t}).minimalPrimes
  · obtain ⟨hZr, hZm⟩ := hZ
    haveI : Z.IsPrime := hZm.1.1
    have hVZ : V ≤ Z := le_sup_left.trans (le_sup_left.trans hZm.1.2)
    haveI : (Z.map (Ideal.Quotient.mk V)).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hVZ)
    have hZm' : Z ∈ (V ⊔ Ideal.span {t} ⊔ Ideal.span {f}).minimalPrimes := by
      rwa [sup_right_comm]
    have h := isLocData_atPrime_quot V Z hVZ
    have hex : ∀ Q : Ideal (MRingOver F ι), Q.IsPrime → V ≤ Q → Q ≤ Z →
        ∃ p : Ideal (Localization.AtPrime (Z.map (Ideal.Quotient.mk V))), p.IsPrime ∧
          p.comap (algebraMap (MRingOver F ι) _) = Q :=
      fun Q hQ hVQ hQZ => exists_prime_comap_atPrime_quot V Z Q hQ hVQ hQZ
    have hdim := h.ringKrullDim_eq_two hVZ hex hfV hZm
      (fun W hW hWZ => hft W ⟨hW, isRelevant_of_le hZr hWZ⟩)
    have hlen := length_quot_ne_top_of_mem_minimalPrimes _
      (h.maximalIdeal_mem_minimalPrimes (hex Z inferInstance hVZ le_rfl) hZm)
    have key := (len2 _ _ _ hdim (fun e => hfV ((h.map_eq_zero_iff hVZ f).mp e))
      (fun e => htV ((h.map_eq_zero_iff hVZ t).mp e)) hlen).2.2
    have e : ((∑ W ∈ (divSupp_finite V f).toFinset, divCycle V f W * divCycle W t Z : ℕ) : ℕ∞) =
        ((∑ W ∈ (divSupp_finite V t).toFinset, divCycle V t W * divCycle W f Z : ℕ) : ℕ∞) := by
      rw [sum_eq_finsum hZr hZm hfV, sum_eq_finsum hZr hZm' htV]
      exact key
    exact_mod_cast e
  · rw [sum_eq_zero_of_not hV hf ht hfV hft hZ,
      sum_eq_zero_of_not hV ht hf htV hft' (by rwa [sup_right_comm])]

theorem swap_cycle {V : Ideal (MRingOver F ι)} {n : ℕ} {f t : MRingOver F ι} {α β : K → ℕ}
    (hV : IsProjVarF V (n + 2)) (hf : IsMultiHomog f α) (ht : IsMultiHomog t β) (hfV : f ∉ V)
    (htV : t ∉ V) (hft : ∀ W ∈ divSupp V f, t ∉ W) :
    ((ratDiv V f 1).sum fun W m => m • ratDiv W t 1) =
      (ratDiv V t 1).sum fun W m => m • ratDiv W f 1 := by
  ext Z
  have h := swap_coeff hV hf ht hfV htV hft (Z := Z)
  simp only [Finsupp.sum, Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul] at h ⊢
  exact h

end ReciprocityTheory.ChartRestriction.G.AI.I1
