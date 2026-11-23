import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockImageArith
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PIntDomainDim
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace BlockImageArithmetic

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]

theorem ringKrullDim_eq (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    ringKrullDim (MRing ι ⧸ mCoordIdeal y) =
      (((Algebra.trdeg ℤ (CoordinateConeArithVar.ratioField y c)).toENat + Fintype.card K + 1 : ℕ∞) :
        WithBot ℕ∞) := by
  have hhor := CoordinateConeArithVar.horizontal y
  have : (mCoordIdeal y).IsPrime := RingHom.ker_isPrime _
  have htr := ConeTrdeg.proof K ι (CoordinateConeArithVar.ratioField y c)
    (CoordinateConeArithVar.ratioPtL y c) (CoordinateConeArithVar.birational y c hc)
    (fun k ↦ ⟨c k, fun h0 ↦ by
      have h1 := congrArg Subtype.val h0
      simp [CoordinateConeArithVar.ratioPtL, CoordinateConeArithVar.ratioPt, hc] at h1⟩)
    (by rw [CoordinateConeArithVar.mCoordIdeal_ratioPtL y c hc]; exact hhor)
  rw [CoordinateConeArithVar.mCoordIdeal_ratioPtL y c hc] at htr
  rw [IntDomainDim.proof (MRing ι ⧸ mCoordIdeal y)
    (CoordinateConeArithVar.algebraMap_injective _ hhor), htr]
  simp only [map_add, map_natCast]

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem div_mem_of_sum (F : IntermediateField ℚ Ω) {A B : Type} [Fintype B] (u : A → Ω) (v : B → Ω)
    (L : Matrix A B ℤ) (hu : ∀ a, u a = ∑ b, (L a b : Ω) * v b) (b₀ : B)
    (hF : ∀ b, v b / v b₀ ∈ F) (a : A) : u a / v b₀ ∈ F := by
  rw [hu, Finset.sum_div]
  refine sum_mem fun b _ ↦ ?_
  rw [mul_div_assoc]
  exact mul_mem (intCast_mem F _) (hF b)

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem ratio_mem_of_sum (F : IntermediateField ℚ Ω) {A B : Type} [Fintype B] (u : A → Ω) (v : B → Ω)
    (L : Matrix A B ℤ) (hu : ∀ a, u a = ∑ b, (L a b : Ω) * v b) (b₀ : B) (hv : v b₀ ≠ 0)
    (hF : ∀ b, v b / v b₀ ∈ F) (a a' : A) : u a / u a' ∈ F := by
  rw [← div_div_div_cancel_right₀ hv (u a) (u a')]
  exact div_mem (div_mem_of_sum F u v L hu b₀ hF a) (div_mem_of_sum F u v L hu b₀ hF a')

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem aeval_mem (F : IntermediateField ℚ Ω) (w : (Σ k, ι k) → Ω) (hw : ∀ p, w p ∈ F) (f : MRing ι) :
    aeval w f ∈ F := by
  induction f using MvPolynomial.induction_on with
  | C a => rw [aeval_C, algebraMap_int_eq, eq_intCast]; exact intCast_mem F a
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p q hp => rw [map_mul, aeval_X]; exact mul_mem hp (hw q)

omit [Fintype K] [CharZero Ω] in

theorem isMultiHomog_X_single [DecidableEq K] (p : Σ k, ι k) :
    IsMultiHomog (X p : MRing ι) (fun k ↦ if k = p.1 then 1 else 0) := by
  intro m hm k
  rw [support_X, Finset.mem_singleton] at hm
  subst hm
  obtain ⟨k', i'⟩ := p
  by_cases h : k = k'
  · subst h
    rw [Finset.sum_eq_single i']
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · simp [h]

omit [CharZero Ω] in

theorem aeval_mul_pow_of_block (y w : (Σ k, ι k) → Ω) (k₀ : K) (z : Ω)
    (hw : ∀ i, w ⟨k₀, i⟩ * z = y ⟨k₀, i⟩) {f : MRing ι} {d : K → ℕ} (hf : IsMultiHomog f d)
    (hd : ∀ k, k ≠ k₀ → d k = 0) : aeval w f * z ^ d k₀ = aeval y f := by
  classical
  conv_rhs => rw [f.as_sum]
  conv_lhs => rw [f.as_sum]
  rw [map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  rw [aeval_monomial, aeval_monomial, mul_assoc]
  congr 1
  have hsum : ∑ p, m p = d k₀ := by
    rw [Fintype.sum_sigma, Finset.sum_eq_single k₀]
    · exact hf m hm k₀
    · intro k _ hk
      rw [hf m hm k, hd k hk]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hzero : ∀ p : Σ k, ι k, p.1 ≠ k₀ → m p = 0 := by
    intro p hp
    have h1 := hf m hm p.1
    rw [hd _ hp] at h1
    exact (Finset.sum_eq_zero_iff.mp h1) p.2 (Finset.mem_univ _)
  rw [Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _), Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _),
    ← hsum, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p _ ↦ ?_
  rw [← mul_pow]
  by_cases hp : p.1 = k₀
  · obtain ⟨k, i⟩ := p
    simp only at hp
    subst hp
    rw [hw i]
  · rw [hzero p hp, pow_zero, pow_zero]

end BlockImageArithmetic

open BlockImageArithmetic in

theorem BlockImageArith.proof : BlockImageArith.Statement := by
  intro D K _ _ ι _ Ω _ _ y k₀ r M N x hY hbir hB _
  classical
  obtain ⟨hK, ⟨_, _, hrel⟩, _, hdim⟩ := hY
  have hnz : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := by
    intro k
    obtain ⟨i, hi⟩ := hrel k
    refine ⟨i, fun h0 ↦ hi ?_⟩
    show mConeMap y (X ⟨k, i⟩) = 0
    simp [mConeMap, h0]
  choose c hc using hnz
  obtain ⟨j₀, hj₀⟩ : ∃ j, x j ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    apply hc k₀
    rw [hB.2 (c k₀)]
    simp [h]
  let c' : ∀ k, GlobalTheory (Fin r) k := fun _ ↦ j₀.2
  have hc' : ∀ k, x ⟨k, c' k⟩ ≠ 0 := fun _ ↦ hj₀
  set Fy := CoordinateConeArithVar.ratioField y c with hFy
  set Fx := CoordinateConeArithVar.ratioField (ι := GlobalTheory (Fin r)) x c' with hFx
  have hxF : ∀ j, x j / x j₀ ∈ Fx := fun j ↦ IntermediateField.subset_adjoin _ _ ⟨j, rfl⟩
  have hLx : Fx ≤ Fy := by
    rw [hFx, IntermediateField.adjoin_le_iff]
    rintro _ ⟨p, rfl⟩
    exact ratio_mem_of_sum Fy x (fun i ↦ y ⟨k₀, i⟩) M hB.1 (c k₀) (hc k₀)
      (fun i ↦ IntermediateField.subset_adjoin _ _ ⟨⟨k₀, i⟩, rfl⟩) p ⟨p.1, c' p.1⟩
  have hLy : Fy ≤ Fx := by
    rw [hFy, IntermediateField.adjoin_le_iff]
    rintro _ ⟨⟨k, i⟩, rfl⟩
    show y ⟨k, i⟩ / y ⟨k, c k⟩ ∈ Fx
    have hyF : ∀ i, y ⟨k₀, i⟩ / x j₀ ∈ Fx := fun i ↦
      div_mem_of_sum Fx (fun i ↦ y ⟨k₀, i⟩) x N hB.2 j₀ hxF i
    let w : (Σ k, ι k) → Ω := fun p ↦ if p.1 = k₀ then y p / x j₀ else 0
    have hwF : ∀ p, w p ∈ Fx := by
      rintro ⟨k', i'⟩
      by_cases h : k' = k₀
      · subst h
        simp only [w, if_true]
        exact hyF i'
      · simp only [w, h, if_false]
        exact zero_mem _
    have hw : ∀ i, w ⟨k₀, i⟩ * x j₀ = y ⟨k₀, i⟩ := fun i ↦ by
      simp only [w, if_true]
      exact div_mul_cancel₀ _ hj₀
    obtain ⟨n, g', h', hg', hh', hh0, heq⟩ := hbir _ (X ⟨k, i⟩) (X ⟨k, c k⟩)
      (isMultiHomog_X_single ⟨k, i⟩) (isMultiHomog_X_single ⟨k, c k⟩)
      (by rw [aeval_X]; exact hc k)
    rw [aeval_X, aeval_X] at heq
    have hd : ∀ k', k' ≠ k₀ → blockDeg k₀ n k' = 0 := fun k' hk' ↦ by simp [blockDeg, hk']
    have e1 := aeval_mul_pow_of_block y w k₀ (x j₀) hw hg' hd
    have e2 := aeval_mul_pow_of_block y w k₀ (x j₀) hw hh' hd
    have hwh : aeval w h' ≠ 0 := fun h0 ↦ hh0 (by rw [← e2, h0, zero_mul])
    have hrat : y ⟨k, i⟩ / y ⟨k, c k⟩ = aeval w g' / aeval w h' := by
      rw [div_eq_div_iff (hc k) hwh]
      apply mul_right_cancel₀ (pow_ne_zero (blockDeg k₀ n k₀) hj₀)
      linear_combination heq + y ⟨k, i⟩ * e2 - y ⟨k, c k⟩ * e1
    rw [hrat]
    exact div_mem (aeval_mem Fx w hwF g') (aeval_mem Fx w hwF h')
  have hLeq : Fy = Fx := le_antisymm hLy hLx
  have hdy := ringKrullDim_eq y c hc
  rw [hdim] at hdy
  rw [coordIdeal_eq_mCoordIdeal]
  refine ⟨⟨()⟩, ⟨RingHom.ker_isPrime _, CoordinateConeArithVar.isMultiHomogIdeal x,
    CoordinateConeArithVar.relevant x c' hc'⟩, CoordinateConeArithVar.horizontal x, ?_⟩
  rw [ringKrullDim_eq x c' hc']
  rw [← hFy, hLeq] at hdy
  generalize (Algebra.trdeg ℤ Fx).toENat = t at hdy ⊢
  have h1 : ((D + 1 + Fintype.card K : ℕ) : ℕ∞) = t + Fintype.card K + 1 := by exact_mod_cast hdy
  induction t using ENat.recTopCoe with
  | top => simp at h1
  | coe t =>
    have h2 : D + 1 + Fintype.card K = t + Fintype.card K + 1 := by exact_mod_cast h1
    have h3 : t = D := by omega
    subst h3
    rw [Fintype.card_unit]
    norm_cast

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
