import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsSemilocRing
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGraphIsometric
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGraphChangeOfModel
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGraphIsometricForms
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace GraphIsometricForms

section Extend

variable {K K₂ M : Type*} [Zero M]

theorem extend_inl_inl (f : K → M) (k : K) : Function.extend (Sum.inl : K → K ⊕ K₂) f 0 (Sum.inl k) = f k :=
  Sum.inl_injective.extend_apply _ _ _

theorem extend_inl_inr (f : K → M) (k : K₂) : Function.extend (Sum.inl : K → K ⊕ K₂) f 0 (Sum.inr k) = 0 := by
  rw [Function.extend_apply' _ _ _ (by rintro ⟨_, h⟩; cases h)]
  rfl

theorem extend_inr_inr (f : K₂ → M) (k : K₂) : Function.extend (Sum.inr : K₂ → K ⊕ K₂) f 0 (Sum.inr k) = f k :=
  Sum.inr_injective.extend_apply _ _ _

theorem extend_inr_inl (f : K₂ → M) (k : K) : Function.extend (Sum.inr : K₂ → K ⊕ K₂) f 0 (Sum.inl k) = 0 := by
  rw [Function.extend_apply' _ _ _ (by rintro ⟨_, h⟩; cases h)]
  rfl

end Extend

section Graph

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)]

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
        ((C : (MRing ι ⧸ P) →+* MvPolynomial K₂ (MRing ι ⧸ P)).comp (Ideal.Quotient.mk P)).comp C :=
      RingHom.ext_int _ _
    exact RingHom.congr_fun e a
  | add p q hp hq => simp [hp, hq]
  | mul_X p n hp => simp [hp, graphMap_X_inlV]

theorem rename_mem_graphIdeal {P : Ideal (MRing ι)} (g : (Σ k, ι₂ k) → MRing ι) {p : MRing ι} (hp : p ∈ P) :
    rename inlV p ∈ graphIdeal P g := by
  rw [graphIdeal, RingHom.mem_ker, graphMap_rename_inlV, Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]

theorem minor_mem (P : Ideal (MRing ι)) (g : (Σ k, ι₂ k) → MRing ι) (k : K₂) (j₁ j₂ : ι₂ k) :
    X (inrV ⟨k, j₁⟩) * rename inlV (g ⟨k, j₂⟩) - X (inrV ⟨k, j₂⟩) * rename inlV (g ⟨k, j₁⟩) ∈
      graphIdeal P g := by
  rw [graphIdeal, RingHom.mem_ker, map_sub, map_mul, map_mul, graphMap_X_inrV, graphMap_X_inrV,
    graphMap_rename_inlV, graphMap_rename_inlV]
  ring

def num (g : (Σ k, ι₂ k) → MRing ι) (j : ∀ k, ι₂ k) (a : K₂ → ℤ) : MRing (Sum.elim ι ι₂) :=
  ∏ k, rename inlV (g ⟨k, j k⟩) ^ (a k).toNat * X (inrV ⟨k, j k⟩) ^ (-a k).toNat

def den (g : (Σ k, ι₂ k) → MRing ι) (j : ∀ k, ι₂ k) (a : K₂ → ℤ) : MRing (Sum.elim ι ι₂) :=
  ∏ k, X (inrV ⟨k, j k⟩) ^ (a k).toNat * rename inlV (g ⟨k, j k⟩) ^ (-a k).toNat

theorem wh_form [DecidableEq K] [DecidableEq K₂] {g : (Σ k, ι₂ k) → MRing ι} {δ : K₂ → K → ℕ}
    (hg : ∀ q, IsMultiHomog (g q) (δ q.1)) (q : Σ k, ι₂ k) :
    IsWeightedHomogeneous (GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight (Sum.elim ι ι₂))
      (rename inlV (g q)) (Function.extend Sum.inl (δ q.1) 0) :=
  (GroundTheory.Heights₂.Heights.Bridge.isMultiHomog_iff _ _).mpr
    (GroundTheory.Heights₂.Heights.Inter.rename_isMultiHomog isBlockMap_inl (hg q))

theorem isMultiHomog_num [DecidableEq K] [DecidableEq K₂] {g : (Σ k, ι₂ k) → MRing ι} {δ : K₂ → K → ℕ}
    (hg : ∀ q, IsMultiHomog (g q) (δ q.1)) (j : ∀ k, ι₂ k) (a : K₂ → ℤ) :
    IsMultiHomog (num g j a)
      (∑ k, ((a k).toNat • Function.extend Sum.inl (δ k) 0 + (-a k).toNat • Pi.single (Sum.inr k) 1)) := by
  refine (GroundTheory.Heights₂.Heights.Bridge.isMultiHomog_iff _ _).mp ?_
  exact IsWeightedHomogeneous.prod _ _ _ fun k _ =>
    ((wh_form hg ⟨k, j k⟩).pow _).mul ((isWeightedHomogeneous_X ℤ _ _).pow _)

theorem isMultiHomog_den [DecidableEq K] [DecidableEq K₂] {g : (Σ k, ι₂ k) → MRing ι} {δ : K₂ → K → ℕ}
    (hg : ∀ q, IsMultiHomog (g q) (δ q.1)) (j : ∀ k, ι₂ k) (a : K₂ → ℤ) :
    IsMultiHomog (den g j a)
      (∑ k, ((a k).toNat • Pi.single (Sum.inr k) 1 + (-a k).toNat • Function.extend Sum.inl (δ k) 0)) := by
  refine (GroundTheory.Heights₂.Heights.Bridge.isMultiHomog_iff _ _).mp ?_
  exact IsWeightedHomogeneous.prod _ _ _ fun k _ =>
    ((isWeightedHomogeneous_X ℤ _ _).pow _).mul ((wh_form hg ⟨k, j k⟩).pow _)

theorem num_den_not_mem {P : Ideal (MRing ι)} (hP : P.IsPrime) (g : (Σ k, ι₂ k) → MRing ι) {j : ∀ k, ι₂ k}
    (hj : ∀ k, g ⟨k, j k⟩ ∉ P) (a : K₂ → ℤ) :
    num g j a ∉ graphIdeal P g ∧ den g j a ∉ graphIdeal P g := by
  have := Ideal.Quotient.isDomain P
  have h1 : ∀ k, (C (Ideal.Quotient.mk P (g ⟨k, j k⟩)) : MvPolynomial K₂ (MRing ι ⧸ P)) ≠ 0 := by
    intro k
    rw [Ne, MvPolynomial.C_eq_zero, Ideal.Quotient.eq_zero_iff_mem]
    exact hj k
  have h2 : ∀ k, (C (Ideal.Quotient.mk P (g ⟨k, j k⟩)) * X k : MvPolynomial K₂ (MRing ι ⧸ P)) ≠ 0 :=
    fun k => mul_ne_zero (h1 k) (X_ne_zero _)
  constructor
  · rw [num, graphIdeal, RingHom.mem_ker]
    simp only [map_prod, map_mul, map_pow, graphMap_rename_inlV, graphMap_X_inrV]
    exact Finset.prod_ne_zero_iff.mpr fun k _ => mul_ne_zero (pow_ne_zero _ (h1 k)) (pow_ne_zero _ (h2 k))
  · rw [den, graphIdeal, RingHom.mem_ker]
    simp only [map_prod, map_mul, map_pow, graphMap_rename_inlV, graphMap_X_inrV]
    exact Finset.prod_ne_zero_iff.mpr fun k _ => mul_ne_zero (pow_ne_zero _ (h2 k)) (pow_ne_zero _ (h1 k))

theorem exists_unit {P : Ideal (MRing ι)} {g : (Σ k, ι₂ k) → MRing ι} (hBP : IsBasePtFree P g)
    (j : ∀ k, ι₂ k) (a : K₂ → ℤ) {W : Ideal (MRing (Sum.elim ι ι₂))} (hW : W.IsPrime)
    (hΓW : graphIdeal P g ≤ W) (hrel : IsRelevant W) :
    ∃ u v, u ∉ W ∧ v ∉ W ∧ u * num g j a - v * den g j a ∈ graphIdeal P g := by
  have hlin : ∀ k, ∃ j', rename inlV (g ⟨k, j'⟩) ∉ W := by
    intro k
    by_contra hall
    push Not at hall
    choose i hi using fun k' => hrel (Sum.inl k')
    obtain ⟨N, hN⟩ := hBP k i
    have hle : P ⊔ Ideal.span (Set.range fun j' : ι₂ k => g ⟨k, j'⟩) ≤
        W.comap (rename (inlV (ι₂ := ι₂)) : MRing ι →ₐ[ℤ] MRing (Sum.elim ι ι₂)) :=
      sup_le (fun p hp => hΓW (rename_mem_graphIdeal g hp))
        (Ideal.span_le.mpr (Set.range_subset_iff.mpr hall))
    have hmem := hle hN
    rw [Ideal.mem_comap, map_pow, map_prod] at hmem
    obtain ⟨k', -, hk'⟩ := Ideal.IsPrime.prod_mem_iff.mp (hW.mem_of_pow_mem N hmem)
    rw [rename_X] at hk'
    exact hi k' hk'
  choose j' hj' using hlin
  have hy : ∀ k, X (inrV ⟨k, j' k⟩) ∉ W := by
    intro k hyk
    obtain ⟨j'', hj''⟩ := hrel (Sum.inr k)
    have hm := hΓW (minor_mem P g k j'' (j' k))
    have hprod : X (inrV ⟨k, j''⟩) * rename inlV (g ⟨k, j' k⟩) ∈ W := by
      have h := W.add_mem hm (W.mul_mem_right (rename inlV (g ⟨k, j''⟩)) hyk)
      rwa [sub_add_cancel] at h
    rcases hW.mem_or_mem hprod with h | h
    · exact hj'' h
    · exact hj' k h
  refine ⟨∏ k, X (inrV ⟨k, j' k⟩) ^ (a k).toNat * rename inlV (g ⟨k, j' k⟩) ^ (-a k).toNat,
    ∏ k, rename inlV (g ⟨k, j' k⟩) ^ (a k).toNat * X (inrV ⟨k, j' k⟩) ^ (-a k).toNat, ?_, ?_, ?_⟩
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

end Graph

theorem proof : GraphIsometricForms.Statement := by
  intro K _ ι _ K₂ _ ι₂ _ P d g δ B₁ B B₁' B' hP hgh hBP ha hh hpl hpr
  classical
  have hPp : P.IsPrime := hP.2.1.1
  choose j hj using GraphChangeOfModel.exists_form_not_mem hP hBP
  obtain ⟨hf, hg⟩ := num_den_not_mem hPp g hj B.a
  refine ⟨num g j B.a, den g j B.a, _, _, isMultiHomog_num hgh j B.a, isMultiHomog_den hgh j B.a, hf, hg, ?_,
    GraphIsometric.divCycle_eq_of_local fun W hW hΓW hrel => exists_unit hBP j B.a hW hΓW hrel, ?_⟩
  · intro x
    rw [hpl.1, hpr.1]
    rcases x with k | k
    · rw [pullDeg, pullDeg, extend_inl_inl, extend_inr_inl, ha k]
      simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, extend_inl_inl, Pi.single_apply,
        reduceCtorEq, if_false, mul_zero, add_zero, zero_add]
      push_cast
      rw [← Finset.sum_sub_distrib, sub_zero]
      refine Finset.sum_congr rfl fun k₂ _ => ?_
      rw [← sub_mul, Int.toNat_sub_toNat_neg]
    · rw [pullDeg, pullDeg, extend_inl_inr, extend_inr_inr]
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
      exact hz.2 _ (rename_mem_graphIdeal g hp)
    have hlin : ∀ q, eval z (map (Int.castRingHom ℂ) (rename inlV (g q))) = formApply g x q := by
      intro q
      rw [hev]
      rfl
    have hyev : ∀ q, eval z (map (Int.castRingHom ℂ) (X (inrV q) : MRing (Sum.elim ι ι₂))) = y q := by
      intro q
      simp [hydef]
    have hminor : ∀ k (j₁ j₂ : ι₂ k),
        y ⟨k, j₁⟩ * formApply g x ⟨k, j₂⟩ = y ⟨k, j₂⟩ * formApply g x ⟨k, j₁⟩ := by
      intro k j₁ j₂
      have h := hz.2 _ (minor_mem P g k j₁ j₂)
      simp only [map_sub, map_mul, hlin, hyev] at h
      exact sub_eq_zero.mp h
    have hgx : ∀ k, ∃ j', formApply g x ⟨k, j'⟩ ≠ 0 := by
      intro k
      by_contra hall
      push Not at hall
      choose i hi using hx.1
      obtain ⟨N, hN⟩ := hBP k i
      let φ : MRing ι →+* ℂ := (eval x).comp (map (Int.castRingHom ℂ))
      have hle : P ⊔ Ideal.span (Set.range fun j' : ι₂ k => g ⟨k, j'⟩) ≤ RingHom.ker φ := by
        refine sup_le (fun p hp => RingHom.mem_ker.mpr (hx.2 p hp))
          (Ideal.span_le.mpr (Set.range_subset_iff.mpr fun j' => ?_))
        exact RingHom.mem_ker.mpr (hall j')
      have h0 := RingHom.mem_ker.mp (hle hN)
      have hne : φ ((∏ k', (X ⟨k', i k'⟩ : MRing ι)) ^ N) ≠ 0 := by
        simp only [φ, map_pow, map_prod, RingHom.comp_apply, map_X, eval_X]
        exact pow_ne_zero _ (Finset.prod_ne_zero_iff.mpr fun k' _ => hi k')
      exact hne h0
    choose jx hjx using hgx
    set c : K₂ → ℂ := fun k => y ⟨k, jx k⟩ / formApply g x ⟨k, jx k⟩ with hcdef
    have hyc : ∀ q : Σ k, ι₂ k, y q = c q.1 * formApply g x q := by
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
    have hB' : B'.h z = (∏ k, ‖c k‖ ^ B.a k) * B.h (formApply g x) := by
      rw [hpr.2 z, ← B.smul c _ hc]
      congr 1
      funext q
      exact hyc q
    have hB₁' : B₁'.h z = B.h (formApply g x) := by
      rw [hpl.2 z]
      exact hh x hx
    rw [hB', hB₁', num, den]
    simp only [map_prod, map_mul, map_pow, hlin, hyev, hyc, norm_prod, norm_mul, norm_pow]
    rw [← mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    exact GraphIsometric.norm_factor (norm_ne_zero_iff.mpr (hc k)) _ _

end GraphIsometricForms

end GroundTheory.Heights₂.Heights.HilbertSamuel
