import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionRing
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

set_option linter.unusedSectionVars false

section G1SpanProof

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem chartLat_mul {y : (Σ k, ι k) → Ω} {a : K → ℤ} {n m : ℕ} {s t : Ω} (hs : s ∈ chartLat y a n)
    (ht : t ∈ chartLat y a m) : s * t ∈ chartLat y a (n + m) := by
  intro c hc
  have key : s * t * ∏ k, y ⟨k, c k⟩ ^ (-(((n + m : ℕ) : ℤ) * a k)) =
      (s * ∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k))) * (t * ∏ k, y ⟨k, c k⟩ ^ (-((m : ℤ) * a k))) := by
    have hp : ∏ k, y ⟨k, c k⟩ ^ (-(((n + m : ℕ) : ℤ) * a k)) =
        (∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k))) * ∏ k, y ⟨k, c k⟩ ^ (-((m : ℤ) * a k)) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← zpow_add₀ (hc k)]
      congr 1
      push_cast
      ring
    rw [hp]
    ring
  rw [key]
  exact mul_mem (hs c hc) (ht c hc)

theorem isBoundedH_mono {P : Ideal (MRing ι)} {y : (Σ k, ι k) → Ω} {A : HermLine ι} {τ : ℕ} {C C' : ℝ} {s : Ω}
    (h : IsBoundedH P y A τ C s) (hC : C ≤ C') : IsBoundedH P y A τ C' s := by
  intro dg dh g h' z hg hh hdeg he hz
  refine (h dg dh g h' z hg hh hdeg he hz).trans ?_
  rw [mul_assoc, mul_assoc]
  exact mul_le_mul_of_nonneg_right hC (mul_nonneg (norm_nonneg _) (pow_nonneg (le_of_lt (A.pos z hz.1)) _))

theorem mul_monomial_bounded (hMul : SectionBoundedMul.Statement) {y : (Σ k, ι k) → Ω} {A : HermLine ι} {q : ℕ}
    {w : Fin q → Ω} (hw : ∀ j, w j ∈ chartLat y A.a 1)
    (hsmall : ∀ j, IsSmallH (mCoordIdeal y) y A 1 (w j)) {x : Ω} {n : ℕ} {C : ℝ}
    (hx : x ∈ chartLat y A.a n) (hb : IsBoundedH (mCoordIdeal y) y A n C x) (μ : Fin q → ℕ) :
    x * ∏ j, w j ^ μ j ∈ chartLat y A.a (n + ∑ j, μ j) ∧
      IsBoundedH (mCoordIdeal y) y A (n + ∑ j, μ j) C (x * ∏ j, w j ^ μ j) := by
  have step : ∀ {x' : Ω} {n' : ℕ} (j : Fin q), x' ∈ chartLat y A.a n' →
      IsBoundedH (mCoordIdeal y) y A n' C x' →
      x' * w j ∈ chartLat y A.a (n' + 1) ∧ IsBoundedH (mCoordIdeal y) y A (n' + 1) C (x' * w j) := by
    intro x' n' j hx' hb'
    refine ⟨chartLat_mul hx' (hw j), ?_⟩
    have := hMul K ι Ω y A n' 1 C 1 x' (w j) hx' (hw j) hb' (isBoundedH_one_of_isSmallH (hsmall j))
    rwa [mul_one] at this
  have hpow : ∀ (j : Fin q) (k : ℕ) {x' : Ω} {n' : ℕ}, x' ∈ chartLat y A.a n' →
      IsBoundedH (mCoordIdeal y) y A n' C x' →
      x' * w j ^ k ∈ chartLat y A.a (n' + k) ∧ IsBoundedH (mCoordIdeal y) y A (n' + k) C (x' * w j ^ k) := by
    intro j k
    induction k with
    | zero => intro x' n' hx' hb'; simpa using ⟨hx', hb'⟩
    | succ k ih =>
      intro x' n' hx' hb'
      obtain ⟨h1, h2⟩ := ih hx' hb'
      have := step j h1 h2
      rw [pow_succ, ← mul_assoc, ← add_assoc]
      exact this
  have hS : ∀ S : Finset (Fin q), x * ∏ j ∈ S, w j ^ μ j ∈ chartLat y A.a (n + ∑ j ∈ S, μ j) ∧
      IsBoundedH (mCoordIdeal y) y A (n + ∑ j ∈ S, μ j) C (x * ∏ j ∈ S, w j ^ μ j) := by
    intro S
    classical
    induction S using Finset.induction_on with
    | empty => simpa using ⟨hx, hb⟩
    | insert a S ha ih =>
      obtain ⟨h1, h2⟩ := hpow a (μ a) ih.1 ih.2
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      have e1 : x * (w a ^ μ a * ∏ j ∈ S, w j ^ μ j) = (x * ∏ j ∈ S, w j ^ μ j) * w a ^ μ a := by ring
      have e2 : n + (μ a + ∑ j ∈ S, μ j) = n + ∑ j ∈ S, μ j + μ a := by ring
      rw [e1, e2]
      exact ⟨h1, h2⟩
  exact hS Finset.univ

theorem exists_coord_ne_zero {y : (Σ k, ι k) → Ω} {d : ℕ} (hV : IsArithVar (mCoordIdeal y) d) (k : K) :
    ∃ i, y ⟨k, i⟩ ≠ 0 := by
  obtain ⟨i, hi⟩ := hV.2.1.2.2 k
  refine ⟨i, fun h0 => hi ?_⟩
  show (X ⟨k, i⟩ : MRing ι) ∈ RingHom.ker (mConeMap y)
  rw [RingHom.mem_ker]
  simp [mConeMap, h0]

end G1SpanProof

theorem SuccessiveMinimaSpan.proof (hFin : SectionRingFinite.Statement) (hBd : SectionBounded.Statement)
    (hMul : SectionBoundedMul.Statement) : SuccessiveMinimaSpan.Statement := by
  intro K _ ι _ Ω _ _ y D A P0 _ hV _ hA
  obtain ⟨q, w, hw, hgen, hsmall⟩ := hA.gen
  obtain ⟨r, d, e, he, hspan⟩ :=
    hFin K ι Ω y A.a q w (exists_coord_ne_zero hV) hw hgen
  have hCe : ∀ i, ∃ C : ℝ, IsBoundedH (mCoordIdeal y) y A (d i) C (e i) := fun i =>
    hBd K ι Ω y A q w hw hgen hsmall (d i) (e i) (he i)
  choose Ce hCe using hCe
  refine ⟨∑ i, |Ce i|, fun n => le_antisymm ?_ ?_⟩
  · rw [AddSubgroup.closure_le]
    exact fun s hs => hs.1
  · refine (hspan n).trans (AddSubgroup.closure_mono ?_)
    rintro s ⟨i, μ, hn, rfl⟩
    obtain ⟨h1, h2⟩ := mul_monomial_bounded hMul hw hsmall (he i) (hCe i) μ
    rw [hn] at h1 h2
    refine ⟨h1, isBoundedH_mono h2 ?_⟩
    exact (le_abs_self _).trans
      (Finset.single_le_sum (f := fun i => |Ce i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
