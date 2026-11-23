import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentTraceSeparatingElement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootsOfUnityAndPValuation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultiplicityDifferentEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColengthDvdOfNeZero
open NumberField IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical nonZeroDivisors

namespace GlobalTheory.AbsDifferent

variable {E : Type} [Field E] [NumberField E] {K : Type} [Field K] {w : AbsoluteValue K ℝ}

def ball (hw : IsNonarchimedean w) (φ : E →+* K) (m : ℝ) (hm : 0 ≤ m) : AddSubgroup E where
  carrier := {x | w (φ x) ≤ m}
  add_mem' := by
    intro a b ha hb
    change w (φ (a + b)) ≤ m
    rw [map_add]
    exact (hw _ _).trans (max_le ha hb)
  zero_mem' := by
    change w (φ 0) ≤ m
    simpa using hm
  neg_mem' := by
    intro a ha
    change w (φ (-a)) ≤ m
    rw [map_neg, AbsoluteValue.map_neg]
    exact ha

theorem abs_sum_le (hw : IsNonarchimedean w) (φ : E →+* K) {m : ℝ} (hm : 0 ≤ m) {ι : Type} [Fintype ι]
    (n : ι → ℤ) (v : ι → E) (hv : ∀ i, w (φ (v i)) ≤ m) : w (φ (∑ i, n i • v i)) ≤ m := by
  have : ∑ i, n i • v i ∈ ball hw φ m hm :=
    AddSubgroup.sum_mem _ fun i _ => AddSubgroup.zsmul_mem _ (hv i) _
  exact this

theorem abs_le_one (hw : IsNonarchimedean w) (φ : E →+* K) (x : 𝓞 E) : w (φ x) ≤ 1 := by
  set C : ℝ := ∑ k, w (φ (RingOfIntegers.basis E k : E)) with hC
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun k _ => w.nonneg _
  have hb : ∀ y : 𝓞 E, w (φ y) ≤ C := by
    intro y
    have hy : (y : E) = ∑ k, (RingOfIntegers.basis E).repr y k • (RingOfIntegers.basis E k : E) := by
      conv_lhs => rw [← (RingOfIntegers.basis E).sum_repr y]
      change algebraMap (𝓞 E) E _ = _
      rw [map_sum]
      exact Finset.sum_congr rfl fun k _ => map_zsmul (algebraMap (𝓞 E) E) _ _
    rw [hy]
    exact abs_sum_le hw φ hC0 _ _ fun k =>
      Finset.single_le_sum (f := fun k => w (φ (RingOfIntegers.basis E k : E))) (fun k _ => w.nonneg _)
        (Finset.mem_univ k)
  by_contra hc
  push_neg at hc
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C hc
  have := hb (x ^ n)
  change w (φ (algebraMap (𝓞 E) E (x ^ n))) ≤ C at this
  rw [map_pow, map_pow, map_pow] at this
  exact absurd this (not_le.2 hn)

def smallIdeal (hw : IsNonarchimedean w) (φ : E →+* K) : Ideal (𝓞 E) where
  carrier := {x | w (φ (algebraMap (𝓞 E) E x)) < 1}
  add_mem' := by
    intro a b ha hb
    change w (φ (algebraMap (𝓞 E) E (a + b))) < 1
    rw [map_add, map_add]
    exact (hw _ _).trans_lt (max_lt ha hb)
  zero_mem' := by
    change w (φ (algebraMap (𝓞 E) E 0)) < 1
    simp
  smul_mem' := by
    intro c x hx
    change w (φ (algebraMap (𝓞 E) E (c * x))) < 1
    rw [map_mul, map_mul, map_mul]
    exact (mul_le_of_le_one_left (w.nonneg _) (abs_le_one hw φ c)).trans_lt hx

variable (hw : IsNonarchimedean w) (φ : E →+* K)

theorem mem_smallIdeal (x : 𝓞 E) : x ∈ smallIdeal hw φ ↔ w (φ (algebraMap (𝓞 E) E x)) < 1 := Iff.rfl

theorem abs_eq_one_of_not_mem {x : 𝓞 E} (hx : x ∉ smallIdeal hw φ) : w (φ (algebraMap (𝓞 E) E x)) = 1 :=
  le_antisymm (abs_le_one hw φ x) (not_lt.1 hx)

theorem natCast_mem_smallIdeal {p : ℕ} (hp1 : w (p : K) < 1) : (p : 𝓞 E) ∈ smallIdeal hw φ := by
  rw [mem_smallIdeal, map_natCast, map_natCast]
  exact hp1

theorem smallIdeal_isPrime : (smallIdeal hw φ).IsPrime where
  ne_top' := fun h => by
    have h1 : (1 : 𝓞 E) ∈ smallIdeal hw φ := h ▸ Submodule.mem_top
    rw [mem_smallIdeal, map_one, map_one, map_one] at h1
    exact lt_irrefl _ h1
  mem_or_mem' := by
    intro x y hxy
    by_contra hc
    push_neg at hc
    rw [mem_smallIdeal, map_mul, map_mul, map_mul, abs_eq_one_of_not_mem hw φ hc.1,
      abs_eq_one_of_not_mem hw φ hc.2, mul_one] at hxy
    exact lt_irrefl _ hxy

theorem abs_eq_pow (P : HeightOneSpectrum (𝓞 E)) (hP : P.asIdeal = smallIdeal hw φ) {π : 𝓞 E}
    (hπ : P.intValuation π = WithZero.exp (-1)) {x : 𝓞 E} (hx : x ≠ 0) {n : ℕ}
    (hn : P.intValuation x = WithZero.exp (-(n : ℤ))) :
    w (φ (algebraMap (𝓞 E) E x)) = w (φ (algebraMap (𝓞 E) E π)) ^ n := by
  have hs : P.intValuation x = P.intValuation (π ^ n) := by
    rw [hn, map_pow, hπ, ← WithZero.exp_nsmul]
    simp
  obtain ⟨u, v, hu, hv, huv⟩ := GlobalTheory.HTConst.exists_mul_eq_mul P hx hs
  have h1 := congrArg (fun t => w (φ (algebraMap (𝓞 E) E t))) huv
  simp only [map_mul, map_pow] at h1
  rw [hP] at hu hv
  rw [abs_eq_one_of_not_mem hw φ hu, abs_eq_one_of_not_mem hw φ hv, one_mul, one_mul] at h1
  exact h1.symm

theorem intValuation_natCast {p : ℕ} (hp : p.Prime) (P : HeightOneSpectrum (𝓞 E)) (hpw : (p : 𝓞 E) ∈ P.asIdeal) :
    P.intValuation (p : 𝓞 E) = WithZero.exp (-((Formalism.BasicNotions.eWL E P : ℕ) : ℤ)) := by
  haveI := Fact.mk hp
  have hp0 : (p : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  obtain ⟨n, hn⟩ := GlobalTheory.HTConst.exists_intValuation_eq P hp0
  haveI := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.liesOver_span E p hp P.isPrime hpw
  have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(p : ℤ)}) = Ideal.span {(p : 𝓞 E)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have he : Formalism.BasicNotions.eWL E P = (normalizedFactors (Ideal.span {(p : 𝓞 E)})).count P.asIdeal := by
    rw [Formalism.BasicNotions.eWL, Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count
      (Ideal.span {(p : ℤ)}) P.asIdeal (by rw [hmap]; exact ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.span_nat_ne_bot p), hmap]
  have h1 : (p : 𝓞 E) ∈ P.asIdeal ^ n := (P.intValuation_le_pow_iff_mem _ n).1 hn.le
  have h2 : (p : 𝓞 E) ∉ P.asIdeal ^ (n + 1) := fun hc => by
    have := (P.intValuation_le_pow_iff_mem _ (n + 1)).2 hc
    rw [hn, WithZero.exp_le_exp] at this
    push_cast at this
    omega
  have h3 := Ideal.count_normalizedFactors_eq (p := P.asIdeal) (x := Ideal.span {(p : 𝓞 E)}) (n := n)
    ((Ideal.span_singleton_le_iff_mem _).2 h1) (fun hc => h2 ((Ideal.span_singleton_le_iff_mem _).1 hc))
  rw [hn, he, h3]

include hw in

theorem abs_different [IsGalois ℚ E] {p : ℕ} (hp : p.Prime) (hp1 : w (p : K) < 1) :
    (∀ d ∈ differentIdeal ℤ (𝓞 E), w (φ (algebraMap (𝓞 E) E d)) ≤ w (p : K) ^ GlobalTheory.ShFam.Pad.vDiff E p) ∧
    ∃ d ∈ differentIdeal ℤ (𝓞 E), w (φ (algebraMap (𝓞 E) E d)) = w (p : K) ^ GlobalTheory.ShFam.Pad.vDiff E p := by
  have hp0 : (p : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  let P : HeightOneSpectrum (𝓞 E) := ⟨smallIdeal hw φ, smallIdeal_isPrime hw φ, fun h => by
    have h1 := natCast_mem_smallIdeal hw φ hp1
    rw [h, Ideal.mem_bot] at h1
    exact hp0 h1⟩
  have hP : P.asIdeal = smallIdeal hw φ := rfl
  have hpw : (p : 𝓞 E) ∈ P.asIdeal := natCast_mem_smallIdeal hw φ hp1
  clear_value P
  have hM := GlobalTheory.ShFam.Pad.multiplicity_different_eq E hp P hpw
  set M := multiplicity P.asIdeal (differentIdeal ℤ (𝓞 E)) with hMdef
  have hval := intValuation_natCast hp P hpw
  set e := Formalism.BasicNotions.eWL E P with hedef
  obtain ⟨π, hπ⟩ := P.intValuation_exists_uniformizer
  set t := w (φ (algebraMap (𝓞 E) E π)) with htdef
  have ht0 : 0 ≤ t := w.nonneg _
  have ht1 : t ≤ 1 := abs_le_one hw φ π
  have hte : w (p : K) = t ^ e := by
    have h1 := abs_eq_pow hw φ P hP hπ hp0 hval
    rw [map_natCast, map_natCast] at h1
    exact h1
  have hT : w (p : K) ^ GlobalTheory.ShFam.Pad.vDiff E p = t ^ M := by
    rw [hte, ← Real.rpow_natCast t e, ← Real.rpow_mul ht0, ← hM, Real.rpow_natCast]
  rw [hT]
  have hD0 : differentIdeal ℤ (𝓞 E) ≠ ⊥ := differentIdeal_ne_bot
  have hfin : FiniteMultiplicity P.asIdeal (differentIdeal ℤ (𝓞 E)) :=
    FiniteMultiplicity.of_not_isUnit (by rw [Ideal.isUnit_iff]; exact P.isPrime.ne_top) hD0
  have hle : differentIdeal ℤ (𝓞 E) ≤ P.asIdeal ^ M := Ideal.le_of_dvd (pow_multiplicity_dvd _ _)
  have hnle : ¬ differentIdeal ℤ (𝓞 E) ≤ P.asIdeal ^ (M + 1) := fun h =>
    hfin.not_pow_dvd_of_multiplicity_lt (Nat.lt_succ_self M) (Ideal.dvd_iff_le.2 h)
  obtain ⟨d0, hd0, hk0⟩ := SetLike.not_le_iff_exists.1 hnle
  refine ⟨fun d hd => ?_, d0, hd0, ?_⟩
  · by_cases h0 : d = 0
    · rw [h0, map_zero, map_zero, map_zero]
      exact pow_nonneg ht0 _
    obtain ⟨n, hn⟩ := GlobalTheory.HTConst.exists_intValuation_eq P h0
    have hMn : M ≤ n := by
      have := (P.intValuation_le_pow_iff_mem _ M).2 (hle hd)
      rw [hn, WithZero.exp_le_exp] at this
      omega
    rw [abs_eq_pow hw φ P hP hπ h0 hn]
    exact pow_le_pow_of_le_one ht0 ht1 hMn
  · have h0 : d0 ≠ 0 := fun h => hk0 (h ▸ Submodule.zero_mem _)
    obtain ⟨n, hn⟩ := GlobalTheory.HTConst.exists_intValuation_eq P h0
    have hMn : M ≤ n := by
      have := (P.intValuation_le_pow_iff_mem _ M).2 (hle hd0)
      rw [hn, WithZero.exp_le_exp] at this
      omega
    have hnM : n < M + 1 := by
      by_contra hc
      push_neg at hc
      apply hk0
      refine (P.intValuation_le_pow_iff_mem _ (M + 1)).1 ?_
      rw [hn, WithZero.exp_le_exp]
      push_cast
      omega
    rw [abs_eq_pow hw φ P hP hπ h0 hn, show n = M by omega]

include hw in

theorem abs_le_of_mem_traceDual {m : ℝ} (hm : 0 ≤ m) (h : ∀ k, w (φ ((integralBasis E).traceDual k)) ≤ m)
    {c : E} (hc : c ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E)) : w (φ c) ≤ m := by
  rw [Submodule.mem_traceDual] at hc
  have h1 : ∀ k, ∃ n : ℤ, (n : ℚ) = ((integralBasis E).traceDual).repr c k := by
    intro k
    obtain ⟨n, hn⟩ := hc (integralBasis E k)
      (Submodule.mem_one.mpr ⟨RingOfIntegers.basis E k, (integralBasis_apply E k).symm⟩)
    refine ⟨n, ?_⟩
    rw [Module.Basis.traceDual_repr_apply, ← hn]
    rfl
  choose n hn using h1
  have h2 : c = ∑ k, n k • (integralBasis E).traceDual k := by
    conv_lhs => rw [← ((integralBasis E).traceDual).sum_repr c]
    exact Finset.sum_congr rfl fun k _ => by rw [← hn, Int.cast_smul_eq_zsmul]
  rw [h2]
  exact abs_sum_le hw φ hm _ _ h

theorem one_mem_mul : (1 : E) ∈ IsLocalization.coeSubmodule E (differentIdeal ℤ (𝓞 E)) *
    Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E) := by
  have h := coeIdeal_differentIdeal ℤ ℚ E (𝓞 E)
  have h0 : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 :=
    FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero
  have h1 : ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) *
      FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) = 1 := by
    rw [h, inv_mul_cancel₀ h0]
  have h2 := congrArg (fun I : FractionalIdeal (𝓞 E)⁰ E => (I : Submodule (𝓞 E) E)) h1
  simp only [FractionalIdeal.coe_mul, FractionalIdeal.coe_coeIdeal, FractionalIdeal.coe_dual_one,
    FractionalIdeal.coe_one] at h2
  rw [h2]
  exact Submodule.mem_one.mpr ⟨1, map_one _⟩

theorem abs_traceDual : ∀ (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (K : Type) [Field K] (w : AbsoluteValue K ℝ),
    IsNonarchimedean w → ∀ p : ℕ, p.Prime → w (p : K) < 1 → ∀ φ : E →+* K,
    (∀ k, w (φ ((integralBasis E).traceDual k)) ≤ w (p : K) ^ (-GlobalTheory.ShFam.Pad.vDiff E p)) ∧
      ∃ k, w (φ ((integralBasis E).traceDual k)) = w (p : K) ^ (-GlobalTheory.ShFam.Pad.vDiff E p) := by
  intro E _ _ _ K _ w hw p hp hp1 φ
  obtain ⟨hall, d0, hd0, hd0e⟩ := abs_different hw φ hp hp1
  have hpK : (p : K) ≠ 0 := by
    rw [← map_natCast φ p]
    exact (map_ne_zero φ).2 (Nat.cast_ne_zero.mpr hp.ne_zero)
  have hwp : 0 < w (p : K) := w.pos hpK
  rw [Real.rpow_neg hwp.le]
  set T := w (p : K) ^ GlobalTheory.ShFam.Pad.vDiff E p with hT
  have hT0 : 0 < T := Real.rpow_pos_of_pos hwp _
  have hup : ∀ k, w (φ ((integralBasis E).traceDual k)) ≤ T⁻¹ := by
    intro k
    obtain ⟨c, hc⟩ := GlobalTheory.ColengthDifferent.exists_mul_traceDual hd0 k
    have h1 : w (φ (algebraMap (𝓞 E) E c)) ≤ 1 := abs_le_one hw φ c
    rw [hc, map_mul, map_mul, hd0e] at h1
    rw [← mul_one T⁻¹, le_inv_mul_iff₀ hT0]
    exact h1
  refine ⟨hup, ?_⟩
  haveI : Nonempty (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) := (RingOfIntegers.basis E).index_nonempty
  obtain ⟨k, hk⟩ := Finite.exists_max fun k => w (φ ((integralBasis E).traceDual k))
  refine ⟨k, le_antisymm (hup k) ?_⟩
  set m := w (φ ((integralBasis E).traceDual k))
  have hm : 0 ≤ m := w.nonneg _
  have key : w (φ 1) ≤ T * m := by
    refine Submodule.mul_induction_on (C := fun x => w (φ x) ≤ T * m) one_mem_mul ?_ ?_
    · intro a ha c hc
      obtain ⟨d, hd, rfl⟩ := (IsLocalization.mem_coeSubmodule _ _).mp ha
      rw [map_mul, map_mul]
      exact mul_le_mul (hall d hd) (abs_le_of_mem_traceDual hw φ hm hk hc) (w.nonneg _) hT0.le
    · intro x y hx hy
      rw [map_add]
      exact (hw _ _).trans (max_le hx hy)
  rw [map_one, map_one] at key
  rw [← mul_one T⁻¹, inv_mul_le_iff₀ hT0]
  exact key

end GlobalTheory.AbsDifferent
