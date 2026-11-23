import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsSwapCyclesArith
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsSwap
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.NotRelevantOfDimZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.MemMinimalPrimesOfMemDivSuppDivSupp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1
  ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc

noncomputable section

namespace SwapCyclesAlt

theorem not_lt_lt {R : Type*} [CommRing R] [IsNoetherianRing R] {V W W' : Ideal R} [V.IsPrime]
    [W'.IsPrime] {x : R} (hW : W ∈ (V ⊔ Ideal.span {x}).minimalPrimes) (hVW' : V < W')
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
  haveI : IsDomain (R ⧸ V) := Ideal.Quotient.isDomain V
  rw [Ideal.height_eq_zero_iff_eq_bot] at h0
  apply hVW'.ne
  apply le_antisymm hVW'.le
  intro y hy
  have : q y ∈ W'.map q := Ideal.mem_map_of_mem q hy
  rw [h0, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at this
  exact this

theorem mem_minimalPrimes_of_mem {R : Type*} [CommRing R] [IsNoetherianRing R] {P W : Ideal R}
    [P.IsPrime] {a b : R} (hW : W ∈ (P ⊔ Ideal.span {a}).minimalPrimes) (hbP : b ∉ P)
    (hbW : b ∈ W) : W ∈ (P ⊔ Ideal.span {b}).minimalPrimes := by
  have hPW : P ≤ W := le_sup_left.trans hW.1.2
  refine ⟨⟨hW.1.1, sup_le hPW (Ideal.span_le.mpr (by simpa using hbW))⟩,
    fun Q ⟨hQ, hQle⟩ hQW => ?_⟩
  by_contra hWQ
  have hlt : Q < W := lt_of_le_of_ne hQW fun e => hWQ (le_of_eq e.symm)
  have hbQ : b ∈ Q := hQle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self b))
  have hPQ : P < Q := lt_of_le_of_ne (le_sup_left.trans hQle) fun e => hbP (by rw [e]; exact hbQ)
  haveI := hQ
  exact not_lt_lt hW hPQ hlt

theorem mem_minimalPrimes_sup {R : Type*} [CommRing R] {V W Z : Ideal R} {f t : R}
    (hZ : Z ∈ (V ⊔ Ideal.span {f} ⊔ Ideal.span {t}).minimalPrimes)
    (hW : W ∈ (V ⊔ Ideal.span {f}).minimalPrimes) (hWZ : W ≤ Z) :
    Z ∈ (W ⊔ Ideal.span {t}).minimalPrimes :=
  ⟨⟨hZ.1.1, sup_le hWZ (le_sup_right.trans hZ.1.2)⟩, fun _ ⟨hQ, hQle⟩ hQZ =>
    hZ.2 ⟨hQ, sup_le (hW.1.2.trans (le_sup_left.trans hQle)) (le_sup_right.trans hQle)⟩ hQZ⟩

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isRelevant_of_le {Y Z : Ideal (MRing ι)} (hZ : IsRelevant Z) (hY : Y ≤ Z) : IsRelevant Y :=
  fun k => (hZ k).imp fun _ hi h => hi (hY h)

theorem dim_of_mem_minimalPrimes {P W : Ideal (MRing ι)} [P.IsPrime] {s : MRing ι} {m : ℕ}
    (hP : ringKrullDim (MRing ι ⧸ P) = ((m + 1 : ℕ) : WithBot ℕ∞)) (hs : s ∉ P)
    (hW : W ∈ (P ⊔ Ideal.span {s}).minimalPrimes) :
    ringKrullDim (MRing ι ⧸ W) = (m : WithBot ℕ∞) :=
  withBot_eq_of_add_one (by rw [dim_quot_minimal_add_one P W s hs hW, hP])

theorem not_mem_of_mem_divSupp {P W : Ideal (MRing ι)} [P.IsPrime] {s s' : MRing ι}
    (hs' : s' ∉ P) (hnc : ∀ W, W ∈ divSupp P s → W ∉ divSupp P s') (hW : W ∈ divSupp P s) :
    s' ∉ W :=
  fun h => hnc W hW ⟨mem_minimalPrimes_of_mem hW.1 hs' h, hW.2⟩

theorem mem_minimalPrimes_of_mem_divSupp_divSupp {P W U : Ideal (MRing ι)} [P.IsPrime]
    {s s' : MRing ι} {m : ℕ} (hP : ringKrullDim (MRing ι ⧸ P) = ((m + 2 : ℕ) : WithBot ℕ∞))
    (hs : s ∉ P) (hs' : s' ∉ P) (hnc : ∀ W, W ∈ divSupp P s → W ∉ divSupp P s')
    (hW : W ∈ divSupp P s) (hU : U ∈ divSupp W s') :
    U ∈ (P ⊔ Ideal.span {s} ⊔ Ideal.span {s'}).minimalPrimes := by
  haveI := hW.1.1.1
  have hWd := dim_of_mem_minimalPrimes (m := m + 1) hP hs hW.1
  have hUd := dim_of_mem_minimalPrimes hWd (not_mem_of_mem_divSupp hs' hnc hW) hU.1
  have hWU : W ≤ U := le_sup_left.trans hU.1.1.2
  have hle : P ⊔ Ideal.span {s} ⊔ Ideal.span {s'} ≤ U :=
    sup_le (hW.1.1.2.trans hWU) (le_sup_right.trans hU.1.1.2)
  refine ⟨⟨hU.1.1.1, hle⟩, fun Q ⟨hQ, hQle⟩ hQU => ?_⟩
  by_contra hUQ
  have hlt : Q < U := lt_of_le_of_ne hQU fun e => hUQ (le_of_eq e.symm)
  obtain ⟨W', hW', hW'Q⟩ := Ideal.exists_minimalPrimes_le (le_sup_left.trans hQle)
  have hW'd : W' ∈ divSupp P s := ⟨hW', isRelevant_of_le hU.2 (hW'Q.trans hQU)⟩
  obtain ⟨Q', hQ', hQ'Q⟩ := Ideal.exists_minimalPrimes_le
    (sup_le hW'Q (le_sup_right.trans hQle) : W' ⊔ Ideal.span {s'} ≤ Q)
  haveI := hW'.1.1
  have h1 := dim_of_mem_minimalPrimes (m := m + 1) hP hs hW'
  have h2 := dim_of_mem_minimalPrimes h1 (not_mem_of_mem_divSupp hs' hnc hW'd) hQ'
  haveI := hQ'.1.1
  haveI := hU.1.1.1
  exact DivisorCycleSwap.not_lt_of_dim_eq (hQ'Q.trans_lt hlt) h2 hUd

theorem component_dims {P U : Ideal (MRing ι)} [P.IsPrime] {s s' : MRing ι} {m : ℕ}
    (hP : ringKrullDim (MRing ι ⧸ P) = ((m + 2 : ℕ) : WithBot ℕ∞)) (hs : s ∉ P) (hs' : s' ∉ P)
    (hnc : ∀ W, W ∈ divSupp P s → W ∉ divSupp P s') (hUr : IsRelevant U)
    (hU : U ∈ (P ⊔ Ideal.span {s} ⊔ Ideal.span {s'}).minimalPrimes) :
    ringKrullDim (MRing ι ⧸ U) = (m : WithBot ℕ∞) ∧
      (U.map (Ideal.Quotient.mk P)).IsPrime ∧
      ∀ [(U.map (Ideal.Quotient.mk P)).IsPrime],
        ringKrullDim (Localization.AtPrime (U.map (Ideal.Quotient.mk P))) = 2 := by
  haveI : U.IsPrime := hU.1.1
  obtain ⟨W, hW, hWU⟩ :=
    Ideal.exists_minimalPrimes_le (le_sup_left.trans hU.1.2 : P ⊔ Ideal.span {s} ≤ U)
  have hWd : W ∈ divSupp P s := ⟨hW, isRelevant_of_le hUr hWU⟩
  haveI := hW.1.1
  have h1 := dim_of_mem_minimalPrimes (m := m + 1) hP hs hW
  have h2 := dim_of_mem_minimalPrimes h1 (not_mem_of_mem_divSupp hs' hnc hWd)
    (mem_minimalPrimes_sup hU hW hWU)
  have hPU : P ≤ U := le_sup_left.trans (le_sup_left.trans hU.1.2)
  refine ⟨h2, Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
    (by rw [Ideal.mk_ker]; exact hPU), fun {_} => ?_⟩
  have h := isLocData_atPrime_quot P U hPU
  have hex : ∀ Q : Ideal (MRing ι), Q.IsPrime → P ≤ Q → Q ≤ U →
      ∃ p : Ideal (Localization.AtPrime (U.map (Ideal.Quotient.mk P))), p.IsPrime ∧
        p.comap (algebraMap (MRing ι) _) = Q :=
    fun Q hQ hVQ hQZ => exists_prime_comap_atPrime_quot P U Q hQ hVQ hQZ
  exact h.ringKrullDim_eq_two hPU hex hs hU
    (fun W hW hWU => not_mem_of_mem_divSupp hs' hnc ⟨hW, isRelevant_of_le hUr hWU⟩)

theorem divCycle_of_mem {V W : Ideal (MRing ι)} {f : MRing ι} (hW : W ∈ divSupp V f) :
    divCycle V f W = multAt (V ⊔ Ideal.span {f}) W := by
  classical
  simp [divCycle, Finsupp.ofSupportFinite_coe, hW]

theorem divCycle_of_not_mem {V W : Ideal (MRing ι)} {f : MRing ι} (hW : W ∉ divSupp V f) :
    divCycle V f W = 0 := by
  classical
  simp [divCycle, Finsupp.ofSupportFinite_coe, hW]

theorem mem_divSupp_of_ne_zero {V W : Ideal (MRing ι)} {f : MRing ι} (h : divCycle V f W ≠ 0) :
    W ∈ divSupp V f := by
  by_contra hW
  exact h (divCycle_of_not_mem hW)

theorem cast_multAt {J W : Ideal (MRing ι)} [hW : W.IsPrime] (hJ : W ∈ J.minimalPrimes) :
    ((multAt J W : ℕ) : ℕ∞) = lenAt J W := by
  have e : multAt J W = (locLen (MRing ι ⧸ J) ⟨W, hW⟩).toNat := by simp [multAt, hW, locLen]
  rw [e, ENat.coe_toNat (locLen_ne_top hJ), lenAt_eq]
  rfl

theorem sum_apply_eq (V Z : Ideal (MRing ι)) (f t : MRing ι) :
    ((divCycle V f).sum fun W m => m • divCycle W t) Z =
      ∑ W ∈ (divSupp_finite V f).toFinset, divCycle V f W * divCycle W t Z := by
  classical
  have hs : (divCycle V f).support ⊆ (divSupp_finite V f).toFinset := by
    intro W hW
    rw [Finsupp.mem_support_iff] at hW
    exact (divSupp_finite V f).mem_toFinset.mpr (mem_divSupp_of_ne_zero hW)
  rw [Finsupp.sum_apply, Finsupp.sum_of_support_subset _ hs _ (fun _ _ => by simp)]
  simp only [Finsupp.smul_apply, smul_eq_mul]

theorem sum_eq_zero_of_not {P U : Ideal (MRing ι)} [P.IsPrime] {s s' : MRing ι} {m : ℕ}
    (hP : ringKrullDim (MRing ι ⧸ P) = ((m + 2 : ℕ) : WithBot ℕ∞)) (hs : s ∉ P) (hs' : s' ∉ P)
    (hnc : ∀ W, W ∈ divSupp P s → W ∉ divSupp P s')
    (hU : ¬ (IsRelevant U ∧ U ∈ (P ⊔ Ideal.span {s} ⊔ Ideal.span {s'}).minimalPrimes)) :
    ∑ W ∈ (divSupp_finite P s).toFinset, divCycle P s W * divCycle W s' U = 0 := by
  refine Finset.sum_eq_zero fun W hW => ?_
  rw [Set.Finite.mem_toFinset] at hW
  by_contra hne
  have hU' := mem_divSupp_of_ne_zero (right_ne_zero_of_mul hne)
  exact hU ⟨hU'.2, mem_minimalPrimes_of_mem_divSupp_divSupp hP hs hs' hnc hW hU'⟩

theorem sum_eq_finsum {V Z : Ideal (MRing ι)} [V.IsPrime] [Z.IsPrime] {A : Type} [CommRing A]
    [IsDomain A] [IsNoetherianRing A] [Algebra (MRing ι) A]
    (h : IsLocData (MRing ι) A Z.primeCompl V) (hVZ : V ≤ Z)
    (hex : ∀ Q : Ideal (MRing ι), Q.IsPrime → V ≤ Q → Q ≤ Z →
      ∃ p : Ideal A, p.IsPrime ∧ p.comap (algebraMap (MRing ι) A) = Q)
    {f t : MRing ι} (hZr : IsRelevant Z)
    (hZ : Z ∈ (V ⊔ Ideal.span {f} ⊔ Ideal.span {t}).minimalPrimes) (hfV : f ∉ V) :
    ((∑ W ∈ (divSupp_finite V f).toFinset, divCycle V f W * divCycle W t Z : ℕ) : ℕ∞) =
      ∑ᶠ (p : PrimeSpectrum A) (_ : p.asIdeal.height = 1 ∧ algebraMap (MRing ι) A f ∈ p.asIdeal),
        ordLoc p (algebraMap (MRing ι) A f) * ordMod p (algebraMap (MRing ι) A t) := by
  classical
  have hterm : ∀ W ∈ (divSupp_finite V f).toFinset, divCycle V f W * divCycle W t Z =
      if W ≤ Z then multAt (V ⊔ Ideal.span {f}) W * multAt (W ⊔ Ideal.span {t}) Z else 0 := by
    intro W hW
    rw [Set.Finite.mem_toFinset] at hW
    rw [divCycle_of_mem hW]
    split_ifs with hWZ
    · rw [divCycle_of_mem ⟨mem_minimalPrimes_sup hZ hW.1 hWZ, hZr⟩]
    · rw [divCycle_of_not_mem (fun h' => hWZ (le_sup_left.trans h'.1.1.2)), mul_zero]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter]
  push_cast
  rw [← finsum_mem_coe_finset]
  symm
  refine finsum_mem_eq_of_bijOn (fun p => p.asIdeal.comap (algebraMap (MRing ι) A))
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
    rw [cast_multAt hm, cast_multAt (mem_minimalPrimes_sup hZ hm hle), lenAt_eq, lenAt_eq,
      (h.atPrime p.asIdeal).length_eq f, (h.quot p.asIdeal).length_eq t, ordLoc, ordMod,
      ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply (MRing ι) A (A ⧸ p.asIdeal),
      Ideal.Quotient.algebraMap_eq]

theorem coeff_eq (hlen2 : LocalLengthMultiplicativity.{0}) {P U : Ideal (MRing ι)} [P.IsPrime] {s s' : MRing ι}
    {m : ℕ} (hP : ringKrullDim (MRing ι ⧸ P) = ((m + 2 : ℕ) : WithBot ℕ∞)) (hs : s ∉ P)
    (hs' : s' ∉ P) (hnc : ∀ W, W ∈ divSupp P s → W ∉ divSupp P s') :
    ∑ W ∈ (divSupp_finite P s).toFinset, divCycle P s W * divCycle W s' U =
      ∑ W ∈ (divSupp_finite P s').toFinset, divCycle P s' W * divCycle W s U := by
  classical
  have hnc' : ∀ W, W ∈ divSupp P s' → W ∉ divSupp P s := fun W hW h => hnc W h hW
  by_cases hU : IsRelevant U ∧ U ∈ (P ⊔ Ideal.span {s} ⊔ Ideal.span {s'}).minimalPrimes
  · obtain ⟨hUr, hUm⟩ := hU
    haveI : U.IsPrime := hUm.1.1
    have hPU : P ≤ U := le_sup_left.trans (le_sup_left.trans hUm.1.2)
    haveI : (U.map (Ideal.Quotient.mk P)).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hPU)
    have hUm' : U ∈ (P ⊔ Ideal.span {s'} ⊔ Ideal.span {s}).minimalPrimes := by
      rwa [sup_right_comm]
    have h := isLocData_atPrime_quot P U hPU
    have hex : ∀ Q : Ideal (MRing ι), Q.IsPrime → P ≤ Q → Q ≤ U →
        ∃ p : Ideal (Localization.AtPrime (U.map (Ideal.Quotient.mk P))), p.IsPrime ∧
          p.comap (algebraMap (MRing ι) _) = Q :=
      fun Q hQ hVQ hQZ => exists_prime_comap_atPrime_quot P U Q hQ hVQ hQZ
    have hdim := h.ringKrullDim_eq_two hPU hex hs hUm
      (fun W hW hWU => not_mem_of_mem_divSupp hs' hnc ⟨hW, isRelevant_of_le hUr hWU⟩)
    have hlen := length_quot_ne_top_of_mem_minimalPrimes _
      (h.maximalIdeal_mem_minimalPrimes (hex U inferInstance hPU le_rfl) hUm)
    have key := (hlen2 _ _ _ hdim (fun e => hs ((h.map_eq_zero_iff hPU s).mp e))
      (fun e => hs' ((h.map_eq_zero_iff hPU s').mp e)) hlen).2.2
    have e : ((∑ W ∈ (divSupp_finite P s).toFinset, divCycle P s W * divCycle W s' U : ℕ) : ℕ∞) =
        ((∑ W ∈ (divSupp_finite P s').toFinset, divCycle P s' W * divCycle W s U : ℕ) : ℕ∞) := by
      rw [sum_eq_finsum h hPU hex hUr hUm hs, sum_eq_finsum h hPU hex hUr hUm' hs']
      exact key
    exact_mod_cast e
  · rw [sum_eq_zero_of_not hP hs hs' hnc hU,
      sum_eq_zero_of_not hP hs' hs hnc' (by rwa [sup_right_comm])]

theorem sum_filter (p : Ideal (MRing ι) → Prop) [DecidablePred p] (c : Ideal (MRing ι) →₀ ℕ)
    (D : Ideal (MRing ι) → Ideal (MRing ι) →₀ ℕ) :
    (c.sum fun W m => m • (D W).filter p) = (c.sum fun W m => m • D W).filter p := by
  ext U
  rw [Finsupp.filter_apply, Finsupp.sum_apply, Finsupp.sum_apply]
  split_ifs with hU
  · simp only [Finsupp.smul_apply, Finsupp.filter_apply, if_pos hU]
  · simp [Finsupp.smul_apply, Finsupp.filter_apply, if_neg hU, Finsupp.sum]

theorem divCycle_eq_zero_of_lt_two {P W : Ideal (MRing ι)} [P.IsPrime] {b b' : MRing ι}
    {c c' : K → ℕ} {d : ℕ} (hPmh : IsMultiHomogIdeal P)
    (hPd : ringKrullDim (MRing ι ⧸ P) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞)) (hd : d < 2)
    (hb : IsMultiHomog b c) (hb' : IsMultiHomog b' c') (hbP : b ∉ P) (hW : W ∈ divSupp P b)
    (hb'W : b' ∉ W) : divCycle W b' = 0 := by
  classical
  ext U
  rw [Finsupp.coe_zero, Pi.zero_apply]
  by_contra hne
  have hU := mem_divSupp_of_ne_zero hne
  haveI := hW.1.1.1
  have hWmh := isMultiHomogIdeal_of_mem_minimalPrimes hPmh hb hW.1
  have hUmh := isMultiHomogIdeal_of_mem_minimalPrimes hWmh hb' hU.1
  have h1 := dim_quot_minimal_add_one P W b hbP hW.1
  have h2 := dim_quot_minimal_add_one W U b' hb'W hU.1
  have h3 := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.card_le_dim hU.1.1.1 hUmh hU.2
  have h4 : ((Fintype.card K + 2 : ℕ) : WithBot ℕ∞) ≤ ((d + Fintype.card K : ℕ) : WithBot ℕ∞) :=
    calc ((Fintype.card K + 2 : ℕ) : WithBot ℕ∞)
        = ((Fintype.card K : ℕ) : WithBot ℕ∞) + 1 + 1 := by push_cast; rw [add_assoc]; rfl
      _ ≤ ringKrullDim (MRing ι ⧸ U) + 1 + 1 := by gcongr
      _ = ringKrullDim (MRing ι ⧸ P) := by rw [h2, h1]
      _ = _ := hPd
  have h5 : Fintype.card K + 2 ≤ d + Fintype.card K := by exact_mod_cast h4
  omega

end SwapCyclesAlt

open SwapCyclesAlt

theorem SwapCyclesArith.proof (hlen2 : LocalLengthMultiplicativity.{0}) : SwapCyclesArith.Statement := by
  intro K _ ι _ P n A A' s s' hP hsA hsA' hnc
  obtain ⟨-, ⟨hPp, -, -⟩, -, hPdim⟩ := hP
  haveI := hPp
  have hPd : ringKrullDim (MRing ι ⧸ P) = ((n + Fintype.card K + 2 : ℕ) : WithBot ℕ∞) := by
    rw [hPdim, show n + 2 + Fintype.card K = n + Fintype.card K + 2 by omega]
  obtain ⟨-, -, -, hs⟩ := hsA
  obtain ⟨-, -, -, hs'⟩ := hsA'
  have hcyc : ((divCycle P s).sum fun W m => m • divCycle W s') =
      (divCycle P s').sum fun W m => m • divCycle W s := by
    ext U
    rw [sum_apply_eq, sum_apply_eq]
    exact coeff_eq hlen2 hPd hs hs' hnc
  refine ⟨fun U hUr hU => component_dims hPd hs hs' hnc hUr hU,
    fun W hW U hU => mem_minimalPrimes_of_mem_divSupp_divSupp hPd hs hs' hnc hW hU, hcyc, ?_, ?_⟩
  · classical
    simp only [horCycle]
    rw [sum_filter, sum_filter, hcyc]
  · classical
    simp only [vertCycle]
    rw [sum_filter, sum_filter, hcyc]

theorem SwapCyclesArith.full : SwapCyclesArith.Statement := SwapCyclesArith.proof length_two_generator_quotient

theorem SwapCycles.proof (hlen2 : LocalLengthMultiplicativity.{0}) : SwapCycles.Statement := by
  intro K _ ι _ P d a a' s s' hP ha ha' hs hs' hnc
  obtain ⟨-, ⟨hPp, hPmh, -⟩, -, hPdim⟩ := hP
  haveI := hPp
  rcases Nat.lt_or_ge d 2 with hd | hd
  · have hz : ∀ (b b' : MRing ι) (c c' : K → ℕ), IsMultiHomog b c → IsMultiHomog b' c' → b ∉ P →
        (∀ W ∈ divSupp P b, b' ∉ W) → ((divCycle P b).sum fun W m => m • divCycle W b') = 0 := by
      intro b b' c c' hb hb' hbP hno
      refine Finset.sum_eq_zero fun W hW => ?_
      have hWd := mem_divSupp_of_ne_zero (Finsupp.mem_support_iff.mp hW)
      dsimp only
      rw [divCycle_eq_zero_of_lt_two hPmh hPdim hd hb hb' hbP hWd (hno W hWd), smul_zero]
    rw [hz s s' a a' ha ha' hs (fun W hW => not_mem_of_mem_divSupp hs' hnc hW),
      hz s' s a' a ha' ha hs' (fun W hW => not_mem_of_mem_divSupp hs (fun W h h' => hnc W h' h) hW)]
  · obtain ⟨m, rfl⟩ : ∃ m, d = m + 2 := ⟨d - 2, by omega⟩
    have hPd : ringKrullDim (MRing ι ⧸ P) = ((m + Fintype.card K + 2 : ℕ) : WithBot ℕ∞) := by
      rw [hPdim, show m + 2 + Fintype.card K = m + Fintype.card K + 2 by omega]
    ext U
    rw [sum_apply_eq, sum_apply_eq]
    exact coeff_eq hlen2 hPd hs hs' hnc

theorem SwapCycles.full : SwapCycles.Statement := SwapCycles.proof length_two_generator_quotient

end

end GroundTheory.Heights₂.Heights.Inter
