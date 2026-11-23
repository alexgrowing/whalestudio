import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Cartier
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.IsMultiHomogIdealIff
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChangeOfModel
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace GraphIsometric

section Divisor

variable {K : Type*} [Fintype K] {κ : K → Type*} [∀ k, Fintype (κ k)]

theorem mul_mem_sup_span {P : Ideal (MRing κ)} {f g u v : MRing κ} (huv : u * f - v * g ∈ P) :
    ∀ x ∈ P ⊔ Ideal.span {f}, u * x ∈ P ⊔ Ideal.span {g} := by
  intro x hx
  obtain ⟨p, hp, r, hr, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hr
  have e : u * (p + c * f) = (u * p + c * (u * f - v * g)) + (c * v) * g := by ring
  rw [e]
  exact Submodule.add_mem_sup (P.add_mem (P.mul_mem_left _ hp) (P.mul_mem_left _ huv))
    (Ideal.mem_span_singleton'.mpr ⟨c * v, rfl⟩)

theorem mem_divSupp_and_multAt_eq {P W : Ideal (MRing κ)} {f g u v : MRing κ} (hf : W ∈ divSupp P f)
    (hu : u ∉ W) (hv : v ∉ W) (huv : u * f - v * g ∈ P) :
    W ∈ divSupp P g ∧ multAt (P ⊔ Ideal.span {f}) W = multAt (P ⊔ Ideal.span {g}) W := by
  have hvu : v * g - u * f ∈ P := by
    rw [← neg_sub]
    exact P.neg_mem huv
  have hWp : W.IsPrime := hf.1.1.1
  refine ⟨⟨GroundTheory.Heights₂.Heights.NumbersDVR.mem_minimalPrimes_of_mul_mem hu hv (mul_mem_sup_span huv)
    (mul_mem_sup_span hvu) hf.1, hf.2⟩, ?_⟩
  unfold multAt
  rw [dif_pos hWp, dif_pos hWp,
    GroundTheory.Heights₂.Heights.NumbersDVR.length_localized_eq_of_mul_mem hu hv (mul_mem_sup_span huv)
      (mul_mem_sup_span hvu)]

theorem divCycle_eq_of_local {P : Ideal (MRing κ)} {f g : MRing κ}
    (h : ∀ W : Ideal (MRing κ), W.IsPrime → P ≤ W → IsRelevant W →
      ∃ u v, u ∉ W ∧ v ∉ W ∧ u * f - v * g ∈ P) :
    divCycle P f = divCycle P g := by
  ext W
  simp only [divCycle, Finsupp.ofSupportFinite_coe]
  by_cases hf : W ∈ divSupp P f
  · obtain ⟨u, v, hu, hv, huv⟩ := h W hf.1.1.1 (le_sup_left.trans hf.1.1.2) hf.2
    obtain ⟨hg, e⟩ := mem_divSupp_and_multAt_eq hf hu hv huv
    rw [if_pos hf, if_pos hg, e]
  · by_cases hg : W ∈ divSupp P g
    · obtain ⟨u, v, hu, hv, huv⟩ := h W hg.1.1.1 (le_sup_left.trans hg.1.1.2) hg.2
      exact absurd (mem_divSupp_and_multAt_eq hg hv hu (by rw [← neg_sub]; exact P.neg_mem huv)).1 hf
    · rw [if_neg hf, if_neg hg]

end Divisor

section Graph

variable {K : Type} [Fintype K] {ι ι₂ : K → Type} [∀ k, Fintype (ι k)] [∀ k, Fintype (ι₂ k)]

theorem graphMap_X_inlV (P : Ideal (MRing ι)) (g : (Σ k, ι₂ k) → MRing ι) (p : Σ k, ι k) :
    graphMap P g (X (inlV p)) = C (Ideal.Quotient.mk P (X p)) := by
  obtain ⟨k, i⟩ := p
  simp [graphMap, inlV]

theorem graphMap_X_inrV (P : Ideal (MRing ι)) (g : (Σ k, ι₂ k) → MRing ι) (q : Σ k, ι₂ k) :
    graphMap P g (X (inrV q)) = C (Ideal.Quotient.mk P (g q)) * X q.1 := by
  obtain ⟨k, j⟩ := q
  simp [graphMap, inrV]

theorem graphMap_rename_inlV (P : Ideal (MRing ι)) (g : (Σ k, ι₂ k) → MRing ι) (p : MRing ι) :
    graphMap P g (rename inlV p) = C (Ideal.Quotient.mk P p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    have e : ((graphMap P g).comp (rename (inlV (ι₂ := ι₂))).toRingHom).comp C =
        ((C : (MRing ι ⧸ P) →+* MvPolynomial K (MRing ι ⧸ P)).comp (Ideal.Quotient.mk P)).comp C :=
      RingHom.ext_int _ _
    exact RingHom.congr_fun e a
  | add p q hp hq => simp [hp, hq]
  | mul_X p n hp => simp [hp, graphMap_X_inlV]

theorem minor_mem (P : Ideal (MRing ι)) (A : ∀ k, ι₂ k → ι k → ℤ) (k : K) (j₁ j₂ : ι₂ k) :
    X (inrV ⟨k, j₁⟩) * rename inlV (linForm A ⟨k, j₂⟩) - X (inrV ⟨k, j₂⟩) * rename inlV (linForm A ⟨k, j₁⟩) ∈
      graphIdeal P (linForm A) := by
  rw [graphIdeal, RingHom.mem_ker, map_sub, map_mul, map_mul, graphMap_X_inrV, graphMap_X_inrV,
    graphMap_rename_inlV, graphMap_rename_inlV]
  ring

def num (A : ∀ k, ι₂ k → ι k → ℤ) (j : ∀ k, ι₂ k) (a : K → ℤ) : MRing (Sum.elim ι ι₂) :=
  ∏ k, rename inlV (linForm A ⟨k, j k⟩) ^ (a k).toNat * X (inrV ⟨k, j k⟩) ^ (-a k).toNat

def den (A : ∀ k, ι₂ k → ι k → ℤ) (j : ∀ k, ι₂ k) (a : K → ℤ) : MRing (Sum.elim ι ι₂) :=
  ∏ k, X (inrV ⟨k, j k⟩) ^ (a k).toNat * rename inlV (linForm A ⟨k, j k⟩) ^ (-a k).toNat

theorem wh_lin [DecidableEq K] (A : ∀ k, ι₂ k → ι k → ℤ) (q : Σ k, ι₂ k) :
    IsWeightedHomogeneous (GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight (Sum.elim ι ι₂))
      (rename inlV (linForm A q)) (Pi.single (Sum.inl q.1) 1) := by
  rw [← mem_weightedHomogeneousSubmodule]
  simp only [linForm, map_sum, map_mul, rename_C, rename_X]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [← smul_eq_C_mul]
  exact Submodule.smul_mem _ _ ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr (isWeightedHomogeneous_X ℤ _ _))

theorem isMultiHomog_num [DecidableEq K] (A : ∀ k, ι₂ k → ι k → ℤ) (j : ∀ k, ι₂ k) (a : K → ℤ) :
    IsMultiHomog (num A j a)
      (∑ k, ((a k).toNat • Pi.single (Sum.inl k) 1 + (-a k).toNat • Pi.single (Sum.inr k) 1)) := by
  refine (GroundTheory.Heights₂.Heights.Bridge.isMultiHomog_iff _ _).mp ?_
  exact IsWeightedHomogeneous.prod _ _ _ fun k _ =>
    ((wh_lin A ⟨k, j k⟩).pow _).mul ((isWeightedHomogeneous_X ℤ _ _).pow _)

theorem isMultiHomog_den [DecidableEq K] (A : ∀ k, ι₂ k → ι k → ℤ) (j : ∀ k, ι₂ k) (a : K → ℤ) :
    IsMultiHomog (den A j a)
      (∑ k, ((a k).toNat • Pi.single (Sum.inr k) 1 + (-a k).toNat • Pi.single (Sum.inl k) 1)) := by
  refine (GroundTheory.Heights₂.Heights.Bridge.isMultiHomog_iff _ _).mp ?_
  exact IsWeightedHomogeneous.prod _ _ _ fun k _ =>
    ((isWeightedHomogeneous_X ℤ _ _).pow _).mul ((wh_lin A ⟨k, j k⟩).pow _)

theorem num_den_not_mem {P : Ideal (MRing ι)} (hP : P.IsPrime) (A : ∀ k, ι₂ k → ι k → ℤ) {j : ∀ k, ι₂ k}
    (hj : ∀ k, linForm A ⟨k, j k⟩ ∉ P) (a : K → ℤ) :
    num A j a ∉ graphIdeal P (linForm A) ∧ den A j a ∉ graphIdeal P (linForm A) := by
  have := Ideal.Quotient.isDomain P
  have h1 : ∀ k, (C (Ideal.Quotient.mk P (linForm A ⟨k, j k⟩)) : MvPolynomial K (MRing ι ⧸ P)) ≠ 0 := by
    intro k
    rw [Ne, MvPolynomial.C_eq_zero, Ideal.Quotient.eq_zero_iff_mem]
    exact hj k
  have h2 : ∀ k, (C (Ideal.Quotient.mk P (linForm A ⟨k, j k⟩)) * X k : MvPolynomial K (MRing ι ⧸ P)) ≠ 0 :=
    fun k => mul_ne_zero (h1 k) (X_ne_zero _)
  constructor
  · rw [num, graphIdeal, RingHom.mem_ker]
    simp only [map_prod, map_mul, map_pow, graphMap_rename_inlV, graphMap_X_inrV]
    exact Finset.prod_ne_zero_iff.mpr fun k _ => mul_ne_zero (pow_ne_zero _ (h1 k)) (pow_ne_zero _ (h2 k))
  · rw [den, graphIdeal, RingHom.mem_ker]
    simp only [map_prod, map_mul, map_pow, graphMap_rename_inlV, graphMap_X_inrV]
    exact Finset.prod_ne_zero_iff.mpr fun k _ => mul_ne_zero (pow_ne_zero _ (h2 k)) (pow_ne_zero _ (h1 k))

theorem exists_unit {P : Ideal (MRing ι)} {A : ∀ k, ι₂ k → ι k → ℤ} (hBP : IsBasePtFree P (linForm A))
    (j : ∀ k, ι₂ k) (a : K → ℤ) {W : Ideal (MRing (Sum.elim ι ι₂))} (hW : W.IsPrime)
    (hΓW : graphIdeal P (linForm A) ≤ W) (hrel : IsRelevant W) :
    ∃ u v, u ∉ W ∧ v ∉ W ∧ u * num A j a - v * den A j a ∈ graphIdeal P (linForm A) := by
  have := hW
  have hlin : ∀ k, ∃ j', rename inlV (linForm A ⟨k, j'⟩) ∉ W := by
    intro k
    by_contra hall
    push Not at hall
    choose i hi using fun k' => hrel (Sum.inl k')
    obtain ⟨N, hN⟩ := hBP k i
    have hle : P ⊔ Ideal.span (Set.range fun j' : ι₂ k => linForm A ⟨k, j'⟩) ≤
        W.comap (rename (inlV (ι₂ := ι₂)) : MRing ι →ₐ[ℤ] MRing (Sum.elim ι ι₂)) := by
      refine sup_le (fun p hp => hΓW ?_) (Ideal.span_le.mpr (Set.range_subset_iff.mpr hall))
      rw [graphIdeal, RingHom.mem_ker, graphMap_rename_inlV, Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]
    have hmem := hle hN
    rw [Ideal.mem_comap, map_pow, map_prod] at hmem
    obtain ⟨k', -, hk'⟩ := Ideal.IsPrime.prod_mem_iff.mp (hW.mem_of_pow_mem N hmem)
    rw [rename_X] at hk'
    exact hi k' hk'
  choose j' hj' using hlin
  have hy : ∀ k, X (inrV ⟨k, j' k⟩) ∉ W := by
    intro k hyk
    obtain ⟨j'', hj''⟩ := hrel (Sum.inr k)
    have hm := hΓW (minor_mem P A k j'' (j' k))
    have hprod : X (inrV ⟨k, j''⟩) * rename inlV (linForm A ⟨k, j' k⟩) ∈ W := by
      have h := W.add_mem hm (W.mul_mem_right (rename inlV (linForm A ⟨k, j''⟩)) hyk)
      rwa [sub_add_cancel] at h
    rcases hW.mem_or_mem hprod with h | h
    · exact hj'' h
    · exact hj' k h
  refine ⟨∏ k, X (inrV ⟨k, j' k⟩) ^ (a k).toNat * rename inlV (linForm A ⟨k, j' k⟩) ^ (-a k).toNat,
    ∏ k, rename inlV (linForm A ⟨k, j' k⟩) ^ (a k).toNat * X (inrV ⟨k, j' k⟩) ^ (-a k).toNat, ?_, ?_, ?_⟩
  · intro h
    obtain ⟨k, -, hk⟩ := Ideal.IsPrime.prod_mem_iff.mp h
    rcases hW.mem_or_mem hk with h | h
    · exact hy k (hW.mem_of_pow_mem _ h)
    · exact hj' k (hW.mem_of_pow_mem _ h)
  · intro h
    obtain ⟨k, -, hk⟩ := Ideal.IsPrime.prod_mem_iff.mp h
    rcases hW.mem_or_mem hk with h | h
    · exact hj' k (hW.mem_of_pow_mem _ h)
    · exact hy k (hW.mem_of_pow_mem _ h)
  · rw [graphIdeal, RingHom.mem_ker, map_sub, sub_eq_zero]
    simp only [num, den, map_prod, map_mul, map_pow, graphMap_rename_inlV, graphMap_X_inrV]
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    ring

theorem norm_factor {l : ℝ} (hl : l ≠ 0) (t : ℝ) (e : ℤ) :
    t ^ e.toNat * (l * t) ^ (-e).toNat * l ^ e = (l * t) ^ e.toNat * t ^ (-e).toNat := by
  have he : l ^ e = l ^ ((e.toNat : ℤ) - ((-e).toNat : ℤ)) := by rw [Int.toNat_sub_toNat_neg]
  rw [he, zpow_sub₀ hl, zpow_natCast, zpow_natCast, mul_pow, mul_pow]
  field_simp

end Graph

theorem proof : GraphIsometric.Statement := by
  intro K _ ι ι₂ _ _ P d A B₁ B B₁' B' hP hBP ha hh hpl hpr
  classical
  have hPp : P.IsPrime := hP.2.1.1
  choose j hj using ChangeOfModel.exists_linForm_not_mem hP hBP
  obtain ⟨hf, hg⟩ := num_den_not_mem hPp A hj B.a
  refine ⟨num A j B.a, den A j B.a, _, _, isMultiHomog_num A j B.a, isMultiHomog_den A j B.a, hf, hg, ?_,
    divCycle_eq_of_local fun W hW hΓW hrel => exists_unit hBP j B.a hW hΓW hrel, ?_⟩
  · intro x
    rw [hpl.1, hpr.1, ha]
    rcases x with k | k
    · have e1 : pullDeg Sum.inl B.a (Sum.inl k : K ⊕ K) = B.a k := Sum.inl_injective.extend_apply _ _ _
      have e2 : pullDeg Sum.inr B.a (Sum.inl k : K ⊕ K) = 0 := by
        rw [pullDeg, Function.extend_apply' _ _ _ (by rintro ⟨_, h⟩; cases h)]
        rfl
      rw [e1, e2]
      simp [Finset.sum_apply, Pi.single_apply]
    · have e1 : pullDeg Sum.inl B.a (Sum.inr k : K ⊕ K) = 0 := by
        rw [pullDeg, Function.extend_apply' _ _ _ (by rintro ⟨_, h⟩; cases h)]
        rfl
      have e2 : pullDeg Sum.inr B.a (Sum.inr k : K ⊕ K) = B.a k := Sum.inr_injective.extend_apply _ _ _
      rw [e1, e2]
      simp [Finset.sum_apply, Pi.single_apply]
      omega
  · intro z hz
    set x : (Σ k, ι k) → ℂ := fun p => z (inlV p) with hxdef
    set y : (Σ k, ι₂ k) → ℂ := fun q => z (inrV q) with hydef
    have hev : ∀ p : MRing ι,
        eval z (map (Int.castRingHom ℂ) (rename (inlV (ι₂ := ι₂)) p)) = eval x (map (Int.castRingHom ℂ) p) := by
      intro p
      rw [map_rename, eval_rename]
      rfl
    have hx : x ∈ mcPts P := by
      refine ⟨fun k => hz.1 (Sum.inl k), fun p hp => ?_⟩
      rw [← hev]
      refine hz.2 _ ?_
      rw [graphIdeal, RingHom.mem_ker, graphMap_rename_inlV, Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]
    have hlin : ∀ q, eval z (map (Int.castRingHom ℂ) (rename inlV (linForm A q))) = linApply A x q := by
      intro q
      rw [hev]
      simp [linForm, linApply]
    have hyev : ∀ q, eval z (map (Int.castRingHom ℂ) (X (inrV q) : MRing (Sum.elim ι ι₂))) = y q := by
      intro q
      simp [hydef]
    have hminor : ∀ k (j₁ j₂ : ι₂ k),
        y ⟨k, j₁⟩ * linApply A x ⟨k, j₂⟩ = y ⟨k, j₂⟩ * linApply A x ⟨k, j₁⟩ := by
      intro k j₁ j₂
      have h := hz.2 _ (minor_mem P A k j₁ j₂)
      simp only [map_sub, map_mul, hlin, hyev] at h
      exact sub_eq_zero.mp h
    have hAx : ∀ k, ∃ j', linApply A x ⟨k, j'⟩ ≠ 0 := by
      intro k
      by_contra hall
      push Not at hall
      choose i hi using hx.1
      obtain ⟨N, hN⟩ := hBP k i
      let φ : MRing ι →+* ℂ := (eval x).comp (map (Int.castRingHom ℂ))
      have hle : P ⊔ Ideal.span (Set.range fun j' : ι₂ k => linForm A ⟨k, j'⟩) ≤ RingHom.ker φ := by
        refine sup_le (fun p hp => RingHom.mem_ker.mpr (hx.2 p hp))
          (Ideal.span_le.mpr (Set.range_subset_iff.mpr fun j' => ?_))
        show φ _ = 0
        simpa [φ, linForm, linApply] using hall j'
      have h0 := RingHom.mem_ker.mp (hle hN)
      have hne : φ ((∏ k', (X ⟨k', i k'⟩ : MRing ι)) ^ N) ≠ 0 := by
        simp only [φ, map_pow, map_prod, RingHom.comp_apply, map_X, eval_X]
        exact pow_ne_zero _ (Finset.prod_ne_zero_iff.mpr fun k' _ => hi k')
      exact hne h0
    choose jx hjx using hAx
    set c : K → ℂ := fun k => y ⟨k, jx k⟩ / linApply A x ⟨k, jx k⟩ with hcdef
    have hyc : ∀ q : Σ k, ι₂ k, y q = c q.1 * linApply A x q := by
      rintro ⟨k, j₁⟩
      simp only [hcdef]
      rw [div_mul_eq_mul_div, eq_div_iff (hjx k)]
      exact hminor k j₁ (jx k)
    have hc : ∀ k, c k ≠ 0 := by
      intro k hck
      obtain ⟨j₁, hj₁⟩ := hz.1 (Sum.inr k)
      have h := hyc ⟨k, j₁⟩
      rw [hck, zero_mul] at h
      exact hj₁ h
    have hB' : B'.h z = (∏ k, ‖c k‖ ^ B.a k) * B.h (linApply A x) := by
      rw [hpr.2 z, ← B.smul c _ hc]
      congr 1
      funext q
      exact hyc q
    have hB₁' : B₁'.h z = B.h (linApply A x) := by
      rw [hpl.2 z]
      exact hh x hx
    rw [hB', hB₁', num, den]
    simp only [map_prod, map_mul, map_pow, hlin, hyev, hyc, norm_prod, norm_mul, norm_pow]
    rw [← mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    exact norm_factor (norm_ne_zero_iff.mpr (hc k)) _ _

end GraphIsometric

end GroundTheory.Heights₂.Heights.HilbertSamuel
