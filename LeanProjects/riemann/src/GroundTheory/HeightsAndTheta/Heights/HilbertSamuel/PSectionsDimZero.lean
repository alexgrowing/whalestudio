import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionsDimZero
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PHilbFnValueSpan
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.PCoordCurveAlgebraic
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet

noncomputable section

set_option linter.unusedSectionVars false

namespace SectionsDimZero

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]

def monVal (z : (Σ k, ι k) → Ω) (m : (Σ k, ι k) →₀ ℕ) : Ω :=
  ∏ p, z p ^ m p

def blockDeg (m : (Σ k, ι k) →₀ ℕ) (k : K) : ℕ :=
  ∑ i, m ⟨k, i⟩

def rt (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) : (Σ k, ι k) → Ω :=
  fun p => y p / y ⟨p.1, c p.1⟩

theorem aeval_monomial_int (z : (Σ k, ι k) → Ω) (m : (Σ k, ι k) →₀ ℕ) (q : ℤ) :
    aeval z (monomial m q : MRing ι) = (q : Ω) * monVal z m := by
  rw [aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), eq_intCast]
  rfl

theorem aeval_monomial_rat (z : (Σ k, ι k) → Ω) (m : (Σ k, ι k) →₀ ℕ) (q : ℚ) :
    aeval z (monomial m q : MvPolynomial (Σ k, ι k) ℚ) = q • monVal z m := by
  rw [aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Algebra.smul_def]
  rfl

theorem monVal_eq (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    (m : (Σ k, ι k) →₀ ℕ) :
    monVal y m = monVal (rt y c) m * ∏ k, y ⟨k, c k⟩ ^ blockDeg m k := by
  have h : ∀ p : Σ k, ι k, y p ^ m p = rt y c p ^ m p * y ⟨p.1, c p.1⟩ ^ m p := fun p => by
    rw [← mul_pow, rt, div_mul_cancel₀ _ (hc p.1)]
  simp only [monVal, h, Finset.prod_mul_distrib, blockDeg]
  congr 1
  rw [Fintype.prod_sigma]
  exact Finset.prod_congr rfl fun k _ => Finset.prod_pow_eq_pow_sum Finset.univ (fun i => m ⟨k, i⟩) (y ⟨k, c k⟩)

theorem rt_mem (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (p : Σ k, ι k) : rt y c p ∈ chartRingQ y c :=
  Algebra.subset_adjoin ⟨p, rfl⟩

theorem monVal_mem (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (m : (Σ k, ι k) →₀ ℕ) :
    monVal (rt y c) m ∈ chartRingQ y c :=
  prod_mem fun p _ => pow_mem (rt_mem y c p) _

theorem inv_mem_chart {y : (Σ k, ι k) → Ω} (hP : IsArithVar (mCoordIdeal y) 1) (c : ∀ k, ι k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (k : K) (i : ι k) :
    (y ⟨k, i⟩ / y ⟨k, c k⟩)⁻¹ ∈ chartRingQ y c :=
  Subalgebra.inv_mem_of_algebraic (A := chartRingQ y c) (x := ⟨_, rt_mem y c ⟨k, i⟩⟩)
    (CoordCurveDegree.isAlgebraic_ratio hP c hc ⟨k, i⟩)

theorem zpow_mem_chart {y : (Σ k, ι k) → Ω} (hP : IsArithVar (mCoordIdeal y) 1) (c : ∀ k, ι k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (k : K) (i : ι k) (e : ℤ) :
    (y ⟨k, i⟩ / y ⟨k, c k⟩) ^ e ∈ chartRingQ y c := by
  rcases e with e | e
  · rw [Int.ofNat_eq_natCast, zpow_natCast]
    exact pow_mem (rt_mem y c ⟨k, i⟩) _
  · rw [zpow_negSucc, ← inv_pow]
    exact pow_mem (inv_mem_chart hP c hc k i) _

theorem chart_le {y : (Σ k, ι k) → Ω} (hP : IsArithVar (mCoordIdeal y) 1) (c c' : ∀ k, ι k)
    (hc' : ∀ k, y ⟨k, c' k⟩ ≠ 0) : chartRingQ y c ≤ chartRingQ y c' := by
  refine Algebra.adjoin_le ?_
  rintro _ ⟨p, rfl⟩
  have e : y p / y ⟨p.1, c p.1⟩ = rt y c' p * (y ⟨p.1, c p.1⟩ / y ⟨p.1, c' p.1⟩)⁻¹ := by
    rw [rt, inv_div, div_mul_div_cancel₀ (hc' p.1)]
  show y p / y ⟨p.1, c p.1⟩ ∈ chartRingQ y c'
  rw [e]
  exact mul_mem (rt_mem y c' p) (inv_mem_chart hP c' hc' p.1 (c p.1))

theorem finrank_map_mulRight (L : Subalgebra ℚ Ω) {w : Ω} (hw : w ≠ 0) :
    Module.finrank ℚ ((Subalgebra.toSubmodule L).map (LinearMap.mulRight ℚ w)) = Module.finrank ℚ L := by
  have hinj : Function.Injective (LinearMap.mulRight ℚ w) := fun s t h => by
    simp only [LinearMap.mulRight_apply] at h
    exact mul_right_cancel₀ hw h
  rw [← (Submodule.equivMapOfInjective _ hinj _).finrank_eq, Subalgebra.finrank_toSubmodule]

theorem chartLatQ_eq {y : (Σ k, ι k) → Ω} (hP : IsArithVar (mCoordIdeal y) 1) (c : ∀ k, ι k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (a : K → ℤ) (n : ℕ) :
    chartLatQ y a n = (Subalgebra.toSubmodule (chartRingQ y c)).map
      (LinearMap.mulRight ℚ (∏ k, y ⟨k, c k⟩ ^ ((n : ℤ) * a k))) := by
  have hu : ∀ c' : ∀ k, ι k, (∀ k, y ⟨k, c' k⟩ ≠ 0) →
      (∏ k, y ⟨k, c' k⟩ ^ (-((n : ℤ) * a k))) * ∏ k, y ⟨k, c' k⟩ ^ ((n : ℤ) * a k) = 1 := by
    intro c' hc'
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun k _ => by rw [← zpow_add₀ (hc' k), neg_add_cancel, zpow_zero]
  ext s
  constructor
  · intro hs
    refine Submodule.mem_map.mpr ⟨s * ∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k)), hs c hc, ?_⟩
    rw [LinearMap.mulRight_apply, mul_assoc, hu c hc, mul_one]
  · rintro ⟨t, ht, rfl⟩ c' hc'
    rw [LinearMap.mulRight_apply]
    have e : (∏ k, y ⟨k, c k⟩ ^ ((n : ℤ) * a k)) * ∏ k, y ⟨k, c' k⟩ ^ (-((n : ℤ) * a k)) =
        ∏ k, (y ⟨k, c k⟩ / y ⟨k, c' k⟩) ^ ((n : ℤ) * a k) := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun k _ => by rw [div_zpow, zpow_neg, div_eq_mul_inv]
    rw [mul_assoc, e]
    exact mul_mem (chart_le hP c c' hc' ht) (prod_mem fun k _ => zpow_mem_chart hP c' hc' k (c k) _)

theorem valueSpan_le (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (d : K → ℕ) :
    valueSpan y d ≤ (Subalgebra.toSubmodule (chartRingQ y c)).map
      (LinearMap.mulRight ℚ (∏ k, y ⟨k, c k⟩ ^ d k)) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨g, hg, rfl⟩
  rw [SetLike.mem_coe, g.as_sum, map_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  rw [aeval_monomial_int, monVal_eq y c hc m]
  have hb : ∀ k, blockDeg m k = d k := fun k => hg m hm k
  simp only [hb]
  exact Submodule.mem_map.mpr ⟨((coeff m g : ℤ) : Ω) * monVal (rt y c) m,
    (mul_mem (intCast_mem _ _) (monVal_mem y c m) : _ * _ ∈ chartRingQ y c),
    by rw [LinearMap.mulRight_apply, mul_assoc]⟩

theorem mem_valueSpan (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (d : K → ℕ)
    (m : (Σ k, ι k) →₀ ℕ) (hm : ∀ k, blockDeg m k ≤ d k) :
    monVal (rt y c) m * ∏ k, y ⟨k, c k⟩ ^ d k ∈ valueSpan y d := by
  classical
  set m' : (Σ k, ι k) →₀ ℕ := Finsupp.equivFunOnFinite.symm
    (fun p => m p + if p.2 = c p.1 then d p.1 - blockDeg m p.1 else 0) with hm'_def
  have hm' : ∀ p, m' p = m p + if p.2 = c p.1 then d p.1 - blockDeg m p.1 else 0 := fun p => by
    simp [hm'_def]
  have hdeg : ∀ k, blockDeg m' k = d k := by
    intro k
    have h1 : blockDeg m' k = blockDeg m k + (d k - blockDeg m k) := by
      simp only [blockDeg, hm', Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have := hm k
    omega
  have hextra : ∏ p, rt y c p ^ (if p.2 = c p.1 then d p.1 - blockDeg m p.1 else 0) = 1 := by
    refine Finset.prod_eq_one fun p _ => ?_
    obtain ⟨k, i⟩ := p
    dsimp only
    split_ifs with h
    · subst h
      rw [rt, div_self (hc k), one_pow]
    · exact pow_zero _
  have hval : monVal (rt y c) m' = monVal (rt y c) m := by
    unfold monVal
    simp only [hm', pow_add, Finset.prod_mul_distrib, hextra, mul_one]
  refine Submodule.subset_span ⟨monomial m' 1, ?_, ?_⟩
  · intro e he k
    rw [support_monomial, if_neg one_ne_zero, Finset.mem_singleton] at he
    rw [he]
    exact hdeg k
  · rw [aeval_monomial_int, Int.cast_one, one_mul, monVal_eq y c hc, hval]
    simp only [hdeg]

theorem exists_le_span {y : (Σ k, ι k) → Ω} (hP : IsArithVar (mCoordIdeal y) 1) (c : ∀ k, ι k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) : ∃ D : ℕ, Subalgebra.toSubmodule (chartRingQ y c) ≤
      Submodule.span ℚ {x | ∃ m, (∀ k, blockDeg m k ≤ D) ∧ monVal (rt y c) m = x} := by
  set V : ℕ → Submodule ℚ Ω := fun D =>
    Submodule.span ℚ {x | ∃ m, (∀ k, blockDeg m k ≤ D) ∧ monVal (rt y c) m = x} with hV
  have hmono : Monotone V := fun D D' h => Submodule.span_mono (by
    rintro _ ⟨m, hm, rfl⟩
    exact ⟨m, fun k => (hm k).trans h, rfl⟩)
  have hfin : Module.Finite ℚ (chartRingQ y c) :=
    Algebra.finite_adjoin_of_finite_of_isIntegral (Set.finite_range _) (by
      rintro _ ⟨p, rfl⟩
      exact (CoordCurveDegree.isAlgebraic_ratio hP c hc p).isIntegral)
  have hfg : (Subalgebra.toSubmodule (chartRingQ y c)).FG := Module.Finite.iff_fg.mp hfin
  have hcpt := (CompleteLattice.isCompactElement_iff_le_of_directed_sSup_le _ _).mp
    ((Submodule.fg_iff_compact _).mp hfg)
  obtain ⟨_, ⟨D, rfl⟩, hD⟩ := hcpt (Set.range V) (Set.range_nonempty V)
    (directedOn_range.mpr hmono.directed_le) (by
      intro x hx
      change x ∈ chartRingQ y c at hx
      rw [chartRingQ, Algebra.adjoin_range_eq_range_aeval] at hx
      obtain ⟨f, rfl⟩ := hx
      rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, f.as_sum, map_sum]
      refine Submodule.sum_mem _ fun m _ => ?_
      rw [aeval_monomial_rat]
      refine Submodule.smul_mem _ _ ?_
      exact (le_sSup (Set.mem_range_self (∑ k, blockDeg m k)) : V _ ≤ _) (Submodule.subset_span
        ⟨m, fun k => Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k), rfl⟩))
  exact ⟨D, hD⟩

theorem valueSpan_eq (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (D : ℕ)
    (hD : Subalgebra.toSubmodule (chartRingQ y c) ≤
      Submodule.span ℚ {x | ∃ m, (∀ k, blockDeg m k ≤ D) ∧ monVal (rt y c) m = x})
    (d : K → ℕ) (hd : ∀ k, D ≤ d k) :
    valueSpan y d = (Subalgebra.toSubmodule (chartRingQ y c)).map
      (LinearMap.mulRight ℚ (∏ k, y ⟨k, c k⟩ ^ d k)) := by
  refine le_antisymm (valueSpan_le y c hc d) ?_
  rw [Submodule.map_le_iff_le_comap]
  refine hD.trans (Submodule.span_le.mpr ?_)
  rintro _ ⟨m, hm, rfl⟩
  exact mem_valueSpan y c hc d m fun k => (hm k).trans (hd k)

theorem eventualValue_eq {f : (K → ℤ) → ℤ} {v : ℤ} (h : ∀ᶠ m in atTop, f m = v) :
    NumbersDVR.eventualValue f = v := by
  have hex : ∃ c, ∀ᶠ m in atTop, f m = c := ⟨v, h⟩
  rw [NumbersDVR.eventualValue, dif_pos hex]
  obtain ⟨m, h1, h2⟩ := (hex.choose_spec.and h).exists
  rw [← h1, h2]

end SectionsDimZero

open SectionsDimZero in

theorem SectionsDimZero.proof : SectionsDimZero.Statement := by
  intro K _ ι _ Ω _ _ y a n hP
  classical
  choose c hcX using hP.2.1.2.2
  have hc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k h0 => hcX k (CoordCurveDegree.X_mem_of_eq_zero h0)
  obtain ⟨D, hD⟩ := exists_le_span hP c hc
  rw [chartLatQ_eq hP c hc, finrank_map_mulRight _
    (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hc k))]
  symm
  unfold genDeg NumbersDVR.intNum
  simp only [NumbersDVR.mixedDiff, List.ofFn_zero, List.foldr_nil]
  apply eventualValue_eq
  filter_upwards [eventually_ge_atTop (fun _ : K => (D : ℤ))] with m hm
  have hm0 : ∀ k, (D : ℤ) ≤ m k := hm
  have e : m = fun k => (((m k).toNat : ℕ) : ℤ) := funext fun k => by
    have := hm0 k
    omega
  rw [e, HilbFnValueSpan.proof, valueSpan_eq y c hc D hD _ (fun k => by have := hm0 k; omega),
    finrank_map_mulRight _ (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k))]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
