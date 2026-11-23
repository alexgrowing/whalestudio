import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.MetricsProjectionFormulaNef
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.UnitRatioDivisorSupportEq
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartLatticeNormMembership
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.MemDivSuppOfDivCycleNeZero
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVertFactorSmooth

noncomputable section

namespace RootFieldNumerics.Ref

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)

section SlopeTestRemainingChoices

set_option linter.unusedSectionVars false

open ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem multAt_eqZ (J W : Ideal (MRing ι)) (hW : W.IsPrime) :
    multAt J W = (locLen (MRing ι ⧸ J) ⟨W, hW⟩).toNat := by
  simp [multAt, hW, locLen]

open Classical in
theorem divCycle_applyZ (V W : Ideal (MRing ι)) (f : MRing ι) :
    divCycle V f W = if W ∈ divSupp V f then multAt (V ⊔ Ideal.span {f}) W else 0 := by
  simp only [divCycle, Finsupp.ofSupportFinite_coe]

theorem mem_of_mem_divSuppZ {V W : Ideal (MRing ι)} {f : MRing ι} (hW : W ∈ divSupp V f) : f ∈ W :=
  hW.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))

theorem mem_divSupp_of_memZ {V W : Ideal (MRing ι)} (hV : V.IsPrime) {f g : MRing ι}
    (hgV : g ∉ V) (hW : W ∈ divSupp V f) (hg : g ∈ W) : W ∈ divSupp V g := by
  have hVW : V ≤ W := le_sup_left.trans hW.1.1.2
  refine ⟨⟨⟨hW.1.1.1, sup_le hVW ((Ideal.span_singleton_le_iff_mem _).mpr hg)⟩, fun Q hQ hQW => ?_⟩, hW.2⟩
  exact (eq_of_le_of_mem_minimalPrimes hV hW.1 hQ.1 (le_sup_left.trans hQ.2)
    (hQ.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self g))) hgV hQW).ge

theorem divCycle_eq_zero_of_not_memZ {V W : Ideal (MRing ι)} {f : MRing ι} (h : f ∉ W) : divCycle V f W = 0 := by
  rw [divCycle_applyZ, if_neg fun h2 => h (mem_of_mem_divSuppZ h2)]

theorem divCycle_mulZ {V : Ideal (MRing ι)} (hV : V.IsPrime) {f g : MRing ι}
    (hf : f ∉ V) (hg : g ∉ V) (W : Ideal (MRing ι)) :
    divCycle V (f * g) W = divCycle V f W + divCycle V g W := by
  classical
  have hfg : f * g ∉ V := fun h => (hV.mem_or_mem h).elim hf hg
  simp only [divCycle_applyZ]
  by_cases h : W ∈ divSupp V (f * g)
  · have hWp := h.1.1.1
    have key := locLen_mul hV hf g ⟨W, hWp⟩
    have hfin := locLen_ne_top h.1
    rw [key] at hfin
    rw [if_pos h, multAt_eqZ _ _ hWp, key]
    by_cases hfW : f ∈ W <;> by_cases hgW : g ∈ W
    · rw [if_pos (mem_divSupp_of_memZ hV hf h hfW), if_pos (mem_divSupp_of_memZ hV hg h hgW),
        multAt_eqZ _ _ hWp, multAt_eqZ _ _ hWp, ENat.toNat_add (WithTop.add_ne_top.mp hfin).1
          (WithTop.add_ne_top.mp hfin).2, add_comm]
    · rw [if_pos (mem_divSupp_of_memZ hV hf h hfW), if_neg fun h2 => hgW (mem_of_mem_divSuppZ h2),
        multAt_eqZ _ _ hWp, locLen_quot_eq_zero _ hgW, zero_add, add_zero]
    · rw [if_neg fun h2 => hfW (mem_of_mem_divSuppZ h2), if_pos (mem_divSupp_of_memZ hV hg h hgW),
        multAt_eqZ _ _ hWp, locLen_quot_eq_zero (V := V) (g := f) _ hfW, add_zero, zero_add]
    · exact absurd (hWp.mem_or_mem (mem_of_mem_divSuppZ h)) (by tauto)
  · rw [if_neg h, if_neg fun h2 => h (mem_divSupp_of_memZ hV hfg h2
        (W.mul_mem_right _ (mem_of_mem_divSuppZ h2))),
      if_neg fun h2 => h (mem_divSupp_of_memZ hV hfg h2 (W.mul_mem_left _ (mem_of_mem_divSuppZ h2)))]

theorem pow_not_memZ {V : Ideal (MRing ι)} (hV : V.IsPrime) {f : MRing ι} (hf : f ∉ V) (n : ℕ) : f ^ n ∉ V :=
  fun h => hf (hV.mem_of_pow_mem n h)

theorem divCycle_oneZ (V W : Ideal (MRing ι)) : divCycle V 1 W = 0 := by
  rw [divCycle_applyZ, if_neg]
  intro h
  exact h.1.1.1.ne_top ((Ideal.eq_top_iff_one _).2 (mem_of_mem_divSuppZ h))

theorem divCycle_powZ {V : Ideal (MRing ι)} (hV : V.IsPrime) {f : MRing ι} (hf : f ∉ V) (n : ℕ)
    (W : Ideal (MRing ι)) : divCycle V (f ^ n) W = n * divCycle V f W := by
  induction n with
  | zero => simp [divCycle_oneZ]
  | succ n ih => rw [pow_succ, divCycle_mulZ hV (pow_not_memZ hV hf n) hf, ih]; ring

theorem divCycle_congrZ {V : Ideal (MRing ι)} {f g : MRing ι} (h : f - g ∈ V) (W : Ideal (MRing ι)) :
    divCycle V f W = divCycle V g W := by
  have key : ∀ {a b : MRing ι}, a - b ∈ V → V ⊔ Ideal.span {a} ≤ V ⊔ Ideal.span {b} := by
    intro a b hab
    refine sup_le le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
    have : a = (a - b) + b := by ring
    rw [this]
    exact add_mem (Ideal.mem_sup_left hab) (Ideal.mem_sup_right (Ideal.mem_span_singleton_self b))
  have e : V ⊔ Ideal.span {f} = V ⊔ Ideal.span {g} :=
    le_antisymm (key h) (key (by simpa using V.neg_mem h))
  have e2 : divSupp V f = divSupp V g := by simp only [divSupp, e]
  rw [divCycle_applyZ, divCycle_applyZ, e2, e]

theorem divCycle_le_of_rel {V W : Ideal (MRing ι)} (hV : V.IsPrime) {a b u : MRing ι} (ha : a ∉ V) (hb : b ∉ V)
    (hu : u ∉ W) {n : ℕ} (c : ℕ → MRing ι)
    (hrel : u * a ^ n + ∑ j ∈ Finset.range n, c j * a ^ j * b ^ (n - j) ∈ V) :
    divCycle V b W ≤ divCycle V a W := by
  classical
  by_cases h : W ∈ divSupp V b
  · have hWp := h.1.1.1
    have hVW : V ≤ W := le_sup_left.trans h.1.1.2
    have haW : a ∈ W := SectionOrderAtPoint.mem_of_rel hWp (mem_of_mem_divSuppZ h) hu c (hVW hrel)
    have h' := mem_divSupp_of_memZ hV ha h haW
    rw [divCycle_applyZ, divCycle_applyZ, if_pos h, if_pos h', multAt_eqZ _ _ hWp, multAt_eqZ _ _ hWp]
    exact ENat.toNat_le_toNat
      (SectionOrderAtPoint.locLen_le_of_rel hV ha hb ⟨W, hWp⟩ hVW hu c hrel (locLen_ne_top h.1))
      (locLen_ne_top h'.1)
  · rw [divCycle_applyZ, if_neg h]
    exact Nat.zero_le _

variable {Ω : Type} [Field Ω]

theorem homog_mono (c : ∀ k, ι k) (e : K → ℕ) : IsMultiHomog (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ e k) e :=
  LowerBoundFree.VertFactorSmooth.isMultiHomog_prod_X_pow c e

theorem mono_not_mem {W : Ideal (MRing ι)} (hW : W.IsPrime) (c : ∀ k, ι k)
    (hc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ W) (e : K → ℕ) : (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ e k) ∉ W := by
  intro h
  obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hW)).1 h
  exact pow_not_memZ hW (hc k) _ hk

theorem chart_form (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {x : Ω}
    (hx : x ∈ chartRingZ y c) : ∃ e₀ : K → ℕ, ∀ e : K → ℕ, e₀ ≤ e → ∃ h : MRing ι, IsMultiHomog h e ∧
      aeval y h = x * ∏ k, y ⟨k, c k⟩ ^ e k := by
  classical
  have up : ∀ (x : Ω) (e₀ : K → ℕ), (∃ h : MRing ι, IsMultiHomog h e₀ ∧ aeval y h = x * ∏ k, y ⟨k, c k⟩ ^ e₀ k) →
      ∀ e : K → ℕ, e₀ ≤ e → ∃ h : MRing ι, IsMultiHomog h e ∧ aeval y h = x * ∏ k, y ⟨k, c k⟩ ^ e k := by
    rintro x e₀ ⟨h, hh, he⟩ e hle
    refine ⟨h * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ (e k - e₀ k), ?_, ?_⟩
    · have := LowerBoundFree.isMultiHomog_mul hh (homog_mono c fun k => e k - e₀ k)
      convert this using 1
      funext k
      have : e₀ k ≤ e k := hle k
      simp only [Pi.add_apply]
      omega
    · simp only [map_mul, map_prod, map_pow, aeval_X, he, mul_assoc, ← Finset.prod_mul_distrib, ← pow_add]
      congr 1
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [Nat.add_sub_cancel' (hle k)]
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    refine ⟨fun k => if k = p.1 then 1 else 0, up _ _ ⟨X p, LowerBoundFree.isMultiHomog_X_single p, ?_⟩⟩
    rw [Finset.prod_eq_single p.1 (fun k _ hk => by simp [hk]) (by simp)]
    have := hc p.1
    simp only [aeval_X, if_true, pow_one]
    field_simp
  | algebraMap r =>
    exact ⟨0, up _ _ ⟨C r, LocalRep.isMultiHomog_C r, by simp⟩⟩
  | add a b _ _ ha hb =>
    obtain ⟨e₁, h₁⟩ := ha
    obtain ⟨e₂, h₂⟩ := hb
    refine ⟨e₁ + e₂, fun e he => ?_⟩
    obtain ⟨f, hf, ef⟩ := h₁ e (le_trans le_self_add he)
    obtain ⟨g, hg, eg⟩ := h₂ e (le_trans le_add_self he)
    exact ⟨f + g, LowerBoundFree.isMultiHomog_add hf hg, by rw [map_add, ef, eg, add_mul]⟩
  | mul a b _ _ ha hb =>
    obtain ⟨e₁, h₁⟩ := ha
    obtain ⟨e₂, h₂⟩ := hb
    obtain ⟨f, hf, ef⟩ := h₁ e₁ le_rfl
    obtain ⟨g, hg, eg⟩ := h₂ e₂ le_rfl
    refine ⟨e₁ + e₂, up _ _ ⟨f * g, LowerBoundFree.isMultiHomog_mul hf hg, ?_⟩⟩
    simp only [map_mul, ef, eg, Pi.add_apply, pow_add, Finset.prod_mul_distrib]
    ring

theorem div_le_of_integral (y : (Σ k, ι k) → Ω) (hP : (mCoordIdeal y).IsPrime) {W : Ideal (MRing ι)}
    (hW : W.IsPrime) (c : ∀ k, ι k) (hcW : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ W) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    {a b : MRing ι} {d : K → ℕ} (ha : IsMultiHomog a d) (hb : IsMultiHomog b d)
    (haP : a ∉ mCoordIdeal y) (hbP : b ∉ mCoordIdeal y) {t : Ω} (ht : aeval y a = t * aeval y b)
    (hint : IsIntegral (chartRingZ y c) t) :
    divCycle (mCoordIdeal y) b W ≤ divCycle (mCoordIdeal y) a W := by
  classical
  obtain ⟨p, hpm, hp⟩ := hint
  set n := p.natDegree
  rw [hpm.as_sum] at hp
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum,
    Polynomial.eval₂_mul, Polynomial.eval₂_C] at hp
  choose e₀ he₀ using fun j => chart_form y c hc (p.coeff j).2
  let e : K → ℕ := ∑ j ∈ Finset.range n, e₀ j
  have hex : ∀ j, ∃ h : MRing ι, j ∈ Finset.range n → IsMultiHomog h e ∧
      aeval y h = (p.coeff j : Ω) * ∏ k, y ⟨k, c k⟩ ^ e k := by
    intro j
    by_cases hj : j ∈ Finset.range n
    · obtain ⟨h, hh⟩ := he₀ j e (Finset.single_le_sum (f := e₀) (fun _ _ => zero_le) hj)
      exact ⟨h, fun _ => hh⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose h hh using hex
  refine divCycle_le_of_rel hP haP hbP (mono_not_mem hW c hcW e) (n := n) h ?_
  refine LowerBoundFree.mem_mCoordIdeal_of_aeval_eq_zero y (d := e + n • d) ?_ ?_
  · refine LowerBoundFree.isMultiHomog_add
      (LowerBoundFree.isMultiHomog_mul (homog_mono c e) (SectionOrderAtPoint.isMultiHomog_pow' ha n))
      (SectionOrderAtPoint.isMultiHomog_sum' _ _ fun j hj => ?_)
    have h1 := LowerBoundFree.isMultiHomog_mul (LowerBoundFree.isMultiHomog_mul
      (hh j hj).1 (SectionOrderAtPoint.isMultiHomog_pow' ha j))
      (SectionOrderAtPoint.isMultiHomog_pow' hb (n - j))
    convert h1 using 1
    have hj' : j ≤ n := (Finset.mem_range.mp hj).le
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_assoc]
    rw [← add_mul, Nat.add_sub_cancel' hj']
  · have hsum : ∀ j ∈ Finset.range n,
        aeval y (h j * a ^ j * b ^ (n - j)) = ((∏ k, y ⟨k, c k⟩ ^ e k) *
          aeval y b ^ n) * (algebraMap (chartRingZ y c) Ω (p.coeff j) * t ^ j) := by
      intro j hj
      have hj' : j ≤ n := (Finset.mem_range.mp hj).le
      have e3 : aeval y b ^ n = aeval y b ^ j * aeval y b ^ (n - j) := by
        rw [← pow_add, Nat.add_sub_cancel' hj']
      simp only [map_mul, map_pow, ht, (hh j hj).2]
      rw [e3]
      show _ = _ * ((p.coeff j : Ω) * t ^ j)
      ring
    rw [map_add, map_sum, Finset.sum_congr rfl hsum, ← Finset.mul_sum, map_mul, map_pow, ht, mul_pow]
    simp only [map_prod, map_pow, aeval_X]
    linear_combination ((∏ k, y ⟨k, c k⟩ ^ e k) * aeval y b ^ n) * hp

theorem X_mem_iff (y : (Σ k, ι k) → Ω) (q : Σ k, ι k) : (X q : MRing ι) ∈ mCoordIdeal y ↔ y q = 0 := by
  show mConeMap y (X q) = 0 ↔ _
  simp [mConeMap, X_ne_zero]

theorem C_not_mem {P : Ideal (MRing ι)} (hP : IsHorizontal P) {n : ℤ} (hn : n ≠ 0) : (C n : MRing ι) ∉ P := by
  intro h
  have h2 : n ∈ P.comap (C : ℤ →+* MRing ι) := h
  rw [hP, Ideal.mem_bot] at h2
  exact hn h2

theorem half_bound (y : (Σ k, ι k) → Ω) (hP : (mCoordIdeal y).IsPrime) (hH : IsHorizontal (mCoordIdeal y))
    {q m : ℕ} (hm : 0 < m) {f g : MRing ι} {df dg : K → ℕ} (hf : IsMultiHomog f df) (hg : IsMultiHomog g dg)
    (hfP : f ∉ mCoordIdeal y) (hgP : g ∉ mCoordIdeal y) {u : Ω} (hu : aeval y f = u * aeval y g)
    (hval : ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → ∀ W : ValuationSubring Ω, (∀ p, y p / y ⟨p.1, c p.1⟩ ∈ W) →
      (m : Ω) * (u * ∏ k, y ⟨k, c k⟩ ^ (-((df k : ℤ) - dg k))) ^ q ∈ W) (W : Ideal (MRing ι)) :
    q * divCycle (mCoordIdeal y) g W ≤
      divCycle (mCoordIdeal y) (C (m : ℤ)) W + q * divCycle (mCoordIdeal y) f W := by
  classical
  by_cases h : W ∈ divSupp (mCoordIdeal y) g
  swap
  · rw [divCycle_applyZ _ _ g, if_neg h]
    simp
  have hWp := h.1.1.1
  have hVW : mCoordIdeal y ≤ W := le_sup_left.trans h.1.1.2
  choose c hcW using h.2
  have hcP : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ mCoordIdeal y := fun k hk => hcW k (hVW hk)
  have hc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k hk => hcP k ((X_mem_iff y _).2 hk)
  have hmP : (C (m : ℤ) : MRing ι) ∉ mCoordIdeal y := C_not_mem hH (by exact_mod_cast hm.ne')
  have hint : IsIntegral (chartRingZ y c) ((m : Ω) * (u * ∏ k, y ⟨k, c k⟩ ^ (-((df k : ℤ) - dg k))) ^ q) := by
    refine GlobalTheory.CompanionTheory.Ar.ChartVal.isIntegral_of_forall_valuationSubring Subtype.val_injective _
      fun V hV => hval c hc V fun p => ?_
    exact hV ⟨_, Algebra.subset_adjoin ⟨p, rfl⟩⟩
  have m1 := mono_not_mem hP c hcP dg
  have m2 := mono_not_mem hP c hcP df
  have n1 : f * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ dg k ∉ mCoordIdeal y := fun h => (hP.mem_or_mem h).elim hfP m1
  have n2 : g * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ df k ∉ mCoordIdeal y := fun h => (hP.mem_or_mem h).elim hgP m2
  have n3 := pow_not_memZ hP n1 q
  have n4 := pow_not_memZ hP n2 q
  have n5 : C (m : ℤ) * (f * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ dg k) ^ q ∉ mCoordIdeal y :=
    fun h => (hP.mem_or_mem h).elim hmP n3
  have key := div_le_of_integral y hP hWp c hcW hc (d := q • (df + dg))
    (a := C (m : ℤ) * (f * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ dg k) ^ q)
    (b := (g * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ df k) ^ q)
    (by
      have := LowerBoundFree.isMultiHomog_mul (LocalRep.isMultiHomog_C (ι := ι) (m : ℤ))
        (SectionOrderAtPoint.isMultiHomog_pow' (LowerBoundFree.isMultiHomog_mul hf (homog_mono c dg)) q)
      simpa using this)
    (by
      have := SectionOrderAtPoint.isMultiHomog_pow' (LowerBoundFree.isMultiHomog_mul hg (homog_mono c df)) q
      rwa [add_comm dg df] at this)
    n5 n4 (by
      have e : (∏ k, y ⟨k, c k⟩ ^ dg k) =
          (∏ k, y ⟨k, c k⟩ ^ (-((df k : ℤ) - dg k))) * ∏ k, y ⟨k, c k⟩ ^ df k := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun k _ => ?_
        rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hc k)]
        congr 1
        ring
      simp only [map_mul, map_pow, map_prod, aeval_X, hu, e, map_natCast]
      ring) hint
  rw [divCycle_mulZ hP hmP n3, divCycle_powZ hP n1, divCycle_powZ hP n2, divCycle_mulZ hP hfP m1,
    divCycle_mulZ hP hgP m2, divCycle_eq_zero_of_not_memZ (mono_not_mem hWp c hcW dg),
    divCycle_eq_zero_of_not_memZ (mono_not_mem hWp c hcW df)] at key
  simpa using key

theorem charOf_dvd {W : Ideal (MRing ι)} {n : ℕ} (h : (C (n : ℤ) : MRing ι) ∈ W) : charOf W ∣ n := by
  set I := W.comap (C : ℤ →+* MRing ι)
  have hd : Submodule.IsPrincipal.generator I ∣ (n : ℤ) := (Submodule.IsPrincipal.mem_iff_generator_dvd I).1 h
  exact Int.natAbs_dvd_natAbs.2 hd

theorem div_const_off {P W : Ideal (MRing ι)} {m : ℕ} (hm : 0 < m)
    (h : ¬ ((charOf W).Prime ∧ charOf W ∣ m)) : divCycle P (C (m : ℤ)) W = 0 := by
  classical
  rw [divCycle_applyZ, if_neg]
  intro hW
  have hd := charOf_dvd (mem_of_mem_divSuppZ hW)
  refine h ⟨PB.prime_charOf_of_ne_zero hW.1.1.1 fun h0 => ?_, hd⟩
  rw [h0, zero_dvd_iff] at hd
  omega

theorem div_const_on {P W : Ideal (MRing ι)} (hP : P.IsPrime) (hH : IsHorizontal P) {m : ℕ} (hm : 0 < m)
    (hp : (charOf W).Prime) :
    divCycle P (C (m : ℤ)) W = padicValNat (charOf W) m * divCycle P (C (charOf W : ℤ)) W := by
  set p := charOf W with hpd
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨m', hm'⟩ : p ^ padicValNat p m ∣ m := pow_padicValNat_dvd
  have hm0 : 0 < m' := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hm'; omega
  have hnd : ¬ p ∣ m' := by
    intro hd
    refine pow_succ_padicValNat_not_dvd (p := p) hm.ne' ?_
    rw [pow_succ]
    conv_rhs => rw [hm']
    exact Nat.mul_dvd_mul_left _ hd
  have e : (C (m : ℤ) : MRing ι) = C (p : ℤ) ^ padicValNat p m * C (m' : ℤ) := by
    rw [← map_pow, ← map_mul]
    congr 1
    exact_mod_cast hm'
  have h1 : (C (p : ℤ) : MRing ι) ∉ P := C_not_mem hH (by exact_mod_cast hp.ne_zero)
  have h2 : (C (m' : ℤ) : MRing ι) ∉ P := C_not_mem hH (by exact_mod_cast hm0.ne')
  rw [e, divCycle_mulZ hP (pow_not_memZ hP h1 _) h2, divCycle_powZ hP h1,
    div_const_off hm0 fun h => hnd h.2, add_zero]

end SlopeTestRemainingChoices

theorem div_close {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    (y : (Σ k, ι k) → Ω) {d : ℕ} (hA : IsArithVar (mCoordIdeal y) d) (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime)
    {q m : ℕ} (hq : 0 < q) (hm : 0 < m) (hmT : ∀ p : ℕ, p.Prime → p ∣ m → p ∈ T)
    {f g : MRing ι} {df dg : K → ℕ} (hf : IsMultiHomog f df) (hg : IsMultiHomog g dg)
    (hfP : f ∉ mCoordIdeal y) (hgP : g ∉ mCoordIdeal y) {u : Ω} (hu : aeval y f = u * aeval y g)
    (hval : ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → ∀ W : ValuationSubring Ω, (∀ p, y p / y ⟨p.1, c p.1⟩ ∈ W) →
      (m : Ω) * (u * ∏ k, y ⟨k, c k⟩ ^ (-((df k : ℤ) - dg k))) ^ q ∈ W ∧
      (m : Ω) * ((u * ∏ k, y ⟨k, c k⟩ ^ (-((df k : ℤ) - dg k)))⁻¹) ^ q ∈ W) :
    (∀ W, charOf W ∉ T → divCycle (mCoordIdeal y) f W = divCycle (mCoordIdeal y) g W) ∧
      ∀ W, charOf W ∈ T → |(divCycle (mCoordIdeal y) f W : ℝ) - divCycle (mCoordIdeal y) g W| ≤
        ((padicValNat (charOf W) m : ℝ) / q) * divCycle (mCoordIdeal y) (C (charOf W : ℤ)) W := by
  have hP : (mCoordIdeal y).IsPrime := hA.2.1.1
  have hH : IsHorizontal (mCoordIdeal y) := hA.2.2.1
  have hf0 : aeval y f ≠ 0 := fun h =>
    hfP (GroundTheory.Heights₂.Heights.LowerBoundFree.mem_mCoordIdeal_of_aeval_eq_zero y hf h)
  have hu0 : u ≠ 0 := fun h => hf0 (by rw [hu, h, zero_mul])
  have h1 := half_bound y hP hH hm hf hg hfP hgP hu fun c hc W hW => (hval c hc W hW).1
  have h2 := half_bound y hP hH (q := q) hm hg hf hgP hfP (u := u⁻¹)
    (by rw [hu, ← mul_assoc, inv_mul_cancel₀ hu0, one_mul]) fun c hc W hW => by
      have := (hval c hc W hW).2
      rw [mul_inv, ← Finset.prod_inv_distrib] at this
      convert this using 5 with k
      rw [← zpow_neg]
      congr 1
      ring
  refine ⟨fun W hW => ?_, fun W hW => ?_⟩
  · have h0 : divCycle (mCoordIdeal y) (C (m : ℤ)) W = 0 := div_const_off hm fun h => hW (hmT _ h.1 h.2)
    have a1 := h1 W
    have a2 := h2 W
    rw [h0, zero_add] at a1 a2
    exact Nat.eq_of_mul_eq_mul_left hq (le_antisymm a2 a1)
  · have h0 := div_const_on hP hH hm (hT _ hW)
    have a1 := h1 W
    have a2 := h2 W
    rw [h0] at a1 a2
    have b1 := (Nat.cast_le (α := ℝ)).2 a1
    have b2 := (Nat.cast_le (α := ℝ)).2 a2
    push_cast at b1 b2
    have hq' : (0 : ℝ) < q := by exact_mod_cast hq
    rw [div_mul_eq_mul_div, le_div_iff₀ hq', ← abs_of_pos hq', ← abs_mul, abs_le]
    constructor <;> nlinarith

theorem div_eq_of_unit {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)}
    (hP : P.IsPrime) {f g : MRing ι} (hfP : f ∉ P) (hgP : g ∉ P)
    (h : ∀ W : Ideal (MRing ι), W.IsPrime → P ≤ W → IsRelevant W → ∃ u v : MRing ι, u ∉ W ∧ v ∉ W ∧ u * f - v * g ∈ P) :
    divCycle P f = divCycle P g := by
  classical
  ext W
  by_cases hW : W ∈ divSupp P f ∨ W ∈ divSupp P g
  · have hW' : W.IsPrime ∧ P ≤ W ∧ IsRelevant W := by
      rcases hW with hW | hW <;> exact ⟨hW.1.1.1, le_sup_left.trans hW.1.1.2, hW.2⟩
    obtain ⟨u, v, hu, hv, huv⟩ := h W hW'.1 hW'.2.1 hW'.2.2
    have := divCycle_congrZ huv W
    rwa [divCycle_mulZ hP (fun h => hu (hW'.2.1 h)) hfP, divCycle_mulZ hP (fun h => hv (hW'.2.1 h)) hgP,
      divCycle_eq_zero_of_not_memZ hu, divCycle_eq_zero_of_not_memZ hv, zero_add, zero_add] at this
  · rw [divCycle_applyZ, divCycle_applyZ, if_neg fun h => hW (Or.inl h), if_neg fun h => hW (Or.inr h)]

theorem exists_forms {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    (y : (Σ k, ι k) → Ω) (hB : Birational y) (hy : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) (a : K → ℤ) {u : Ω} (hu : u ≠ 0) :
    ∃ (f g : MRing ι) (df dg : K → ℕ), IsMultiHomog f df ∧ IsMultiHomog g dg ∧ f ∉ mCoordIdeal y ∧
      g ∉ mCoordIdeal y ∧ (∀ k, (df k : ℤ) - dg k = a k) ∧ aeval y f = u * aeval y g := by
  choose c hc using hy
  obtain ⟨d, g, h, hg, hh, h0, e⟩ := hB (u * ∏ k, y ⟨k, c k⟩ ^ (-a k))
  have hn : ∀ b : K → ℕ, (∏ k, y ⟨k, c k⟩ ^ b k) ≠ 0 := fun b =>
    Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)
  have e2 : (∏ k, y ⟨k, c k⟩ ^ (-a k)) * ∏ k, y ⟨k, c k⟩ ^ (a k).toNat = ∏ k, y ⟨k, c k⟩ ^ (-a k).toNat := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hc k)]
    congr 1
    omega
  have eg : aeval y (h * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ (-a k).toNat) ≠ 0 := by
    simp only [map_mul, map_prod, map_pow, aeval_X]
    exact mul_ne_zero h0 (hn _)
  have ef : aeval y (g * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ (a k).toNat) =
      u * aeval y (h * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ (-a k).toNat) := by
    simp only [map_mul, map_prod, map_pow, aeval_X, e, ← e2]
    ring
  refine ⟨_, _, _, _, GroundTheory.Heights₂.Heights.LowerBoundFree.isMultiHomog_mul hg (homog_mono c fun k => (a k).toNat),
    GroundTheory.Heights₂.Heights.LowerBoundFree.isMultiHomog_mul hh (homog_mono c fun k => (-a k).toNat),
    fun hm => ?_, fun hm => eg (GlobalTheory.CompanionTheory.Ar.Giv.aeval_eq_zero_of_mem_mCoordIdeal y hm), fun k => ?_, ef⟩
  · have := GlobalTheory.CompanionTheory.Ar.Giv.aeval_eq_zero_of_mem_mCoordIdeal y hm
    rw [ef] at this
    exact mul_ne_zero hu eg this
  · simp only [Pi.add_apply]
    push_cast
    omega

end RootFieldNumerics.Ref
