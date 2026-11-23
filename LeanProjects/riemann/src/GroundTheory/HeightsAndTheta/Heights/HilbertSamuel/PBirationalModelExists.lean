import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBirationalModelExists
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsMultiHomogX
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

set_option linter.unusedSectionVars false

namespace BirationalModelExists

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isMultiHomog_zero' (a : K → ℕ) : IsMultiHomog (0 : MRing ι) a := by
  intro m hm
  simp at hm

theorem isMultiHomog_add' {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f + g) a := by
  classical
  intro m hm
  rcases Finset.mem_union.1 (support_add hm) with h | h
  exacts [hf m h, hg m h]

theorem isMultiHomog_neg' {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) : IsMultiHomog (-f) a := by
  intro m hm
  rw [support_neg] at hm
  exact hf m hm

theorem aeval_scale {S : Type*} [CommRing S] [Algebra ℤ S] {g : MRing ι} {a : K → ℕ} (hg : IsMultiHomog g a)
    (z : (Σ k, ι k) → S) (u : K → S) :
    aeval (fun p => z p * u p.1) g = aeval z g * ∏ k, u k ^ a k := by
  rw [aeval_def, aeval_def, eval₂_eq', eval₂_eq', Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hprod : ∏ p, (z p * u p.1) ^ m p = (∏ p, z p ^ m p) * ∏ k, u k ^ a k := by
    simp_rw [mul_pow, Finset.prod_mul_distrib]
    congr 1
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, u k ^ m ⟨k, i⟩ = u k ^ a k
    rw [Finset.prod_pow_eq_pow_sum, hg m hm k]
  rw [hprod]
  ring

theorem hom_aeval {S T : Type*} [CommRing S] [CommRing T] [Algebra ℤ S] [Algebra ℤ T] (φ : S →+* T) (z : (Σ k, ι k) → S) (g : MRing ι) :
    φ (aeval z g) = aeval (fun p => φ (z p)) g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p n hp => simp [hp]

variable (P : Ideal (MRing ι)) [P.IsPrime]

def coordClass (p : Σ k, ι k) : FractionRing (MRing ι ⧸ P) :=
  algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P (X p))

theorem aeval_coordClass (g : MRing ι) :
    aeval (coordClass P) g = algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P g) := by
  induction g using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p n hp => simp only [map_mul, hp, aeval_X, coordClass]

theorem aeval_coordClass_eq_zero (g : MRing ι) : aeval (coordClass P) g = 0 ↔ g ∈ P := by
  rw [aeval_coordClass, map_eq_zero_iff _ (IsFractionRing.injective (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P))),
    Ideal.Quotient.eq_zero_iff_mem]

def fnField : Subfield (FractionRing (MRing ι ⧸ P)) where
  carrier := {s | ∃ (d : K → ℕ) (g h : MRing ι), IsMultiHomog g d ∧ IsMultiHomog h d ∧
    aeval (coordClass P) h ≠ 0 ∧ aeval (coordClass P) g = s * aeval (coordClass P) h}
  zero_mem' := ⟨0, 0, 1, isMultiHomog_zero' 0, isMultiHomog_one, by simp, by simp⟩
  one_mem' := ⟨0, 1, 1, isMultiHomog_one, isMultiHomog_one, by simp, by simp⟩
  add_mem' := by
    rintro s t ⟨d, g, h, hg, hh, h0, hs⟩ ⟨d', g', h', hg', hh', h0', ht⟩
    refine ⟨d + d', g * h' + h * g', h * h',
      isMultiHomog_add' (isMultiHomog_mul hg hh') (isMultiHomog_mul hh hg'), isMultiHomog_mul hh hh',
      by simp [h0, h0'], ?_⟩
    simp only [map_add, map_mul, hs, ht]
    ring
  mul_mem' := by
    rintro s t ⟨d, g, h, hg, hh, h0, hs⟩ ⟨d', g', h', hg', hh', h0', ht⟩
    refine ⟨d + d', g * g', h * h', isMultiHomog_mul hg hg', isMultiHomog_mul hh hh', by simp [h0, h0'], ?_⟩
    simp only [map_mul, hs, ht]
    ring
  neg_mem' := by
    rintro s ⟨d, g, h, hg, hh, h0, hs⟩
    exact ⟨d, -g, h, isMultiHomog_neg' hg, hh, h0, by simp [hs]⟩
  inv_mem' := by
    rintro s ⟨d, g, h, hg, hh, h0, hs⟩
    by_cases s0 : s = 0
    · subst s0
      exact ⟨0, 0, 1, isMultiHomog_zero' 0, isMultiHomog_one, by simp, by simp⟩
    · refine ⟨d, h, g, hh, hg, ?_, ?_⟩
      · rw [hs]
        exact mul_ne_zero s0 h0
      · rw [hs, ← mul_assoc, inv_mul_cancel₀ s0, one_mul]

variable {P}

theorem coordClass_ne_zero {p : Σ k, ι k} (hp : (X p : MRing ι) ∉ P) : coordClass P p ≠ 0 := by
  have h := (aeval_coordClass_eq_zero P (X p)).not.2 hp
  rwa [aeval_X] at h

open Classical in

def birPoint (c : ∀ k, ι k) (hc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ P) (p : Σ k, ι k) : fnField P :=
  ⟨coordClass P p / coordClass P ⟨p.1, c p.1⟩,
    ⟨Pi.single p.1 1, X p, X ⟨p.1, c p.1⟩, isMultiHomog_X' p.1 p.2, isMultiHomog_X' p.1 (c p.1),
      by rw [aeval_X]; exact coordClass_ne_zero (hc p.1),
      by rw [aeval_X, aeval_X, div_mul_cancel₀ _ (coordClass_ne_zero (hc p.1))]⟩⟩

theorem coe_birPoint (c : ∀ k, ι k) (hc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ P) (p : Σ k, ι k) :
    (birPoint c hc p : FractionRing (MRing ι ⧸ P)) = coordClass P p / coordClass P ⟨p.1, c p.1⟩ := rfl

theorem coe_aeval_birPoint (c : ∀ k, ι k) (hc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ P) {g : MRing ι} {a : K → ℕ}
    (hg : IsMultiHomog g a) :
    ((aeval (birPoint c hc) g : fnField P) : FractionRing (MRing ι ⧸ P)) =
      aeval (coordClass P) g * ∏ k, (coordClass P ⟨k, c k⟩)⁻¹ ^ a k := by
  have h := hom_aeval (fnField P).subtype (birPoint c hc) g
  have hf : (fun p => (fnField P).subtype (birPoint c hc p)) =
      fun p => coordClass P p * (fun k => (coordClass P ⟨k, c k⟩)⁻¹) p.1 := by
    funext p
    exact div_eq_mul_inv _ _
  rw [hf] at h
  exact h.trans (aeval_scale hg (coordClass P) fun k => (coordClass P ⟨k, c k⟩)⁻¹)

theorem prod_inv_ne_zero (c : ∀ k, ι k) (hc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ P) (a : K → ℕ) :
    ∏ k, (coordClass P ⟨k, c k⟩)⁻¹ ^ a k ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (inv_ne_zero (coordClass_ne_zero (hc k)))

theorem eval_mConeMap_birPoint (c : ∀ k, ι k) (hc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ P) (f : MRing ι) :
    eval₂ (fnField P).subtype (fun k => coordClass P ⟨k, c k⟩) (mConeMap (birPoint c hc) f) =
      aeval (coordClass P) f := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    have e1 := map_intCast (eval₂Hom (fnField P).subtype (fun k => coordClass P ⟨k, c k⟩)) a
    simp only [coe_eval₂Hom] at e1
    simpa [mConeMap] using e1
  | add p q hp hq => simp only [map_add, eval₂_add, hp, hq]
  | mul_X p n hp =>
    have hX : mConeMap (birPoint c hc) (X n) = C (birPoint c hc n) * X n.1 := by simp [mConeMap]
    have e : (fnField P).subtype (birPoint c hc n) * coordClass P ⟨n.1, c n.1⟩ = coordClass P n :=
      div_mul_cancel₀ _ (coordClass_ne_zero (hc n.1))
    rw [map_mul, eval₂_mul, hp, hX, eval₂_mul, eval₂_C, eval₂_X, map_mul, aeval_X, e]

theorem mCoordIdeal_birPoint (hP : IsMultiHomogIdeal P) (c : ∀ k, ι k)
    (hc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ P) : mCoordIdeal (birPoint c hc) = P := by
  apply le_antisymm
  · intro f hf
    rw [mCoordIdeal, RingHom.mem_ker] at hf
    have h := eval_mConeMap_birPoint c hc f
    rw [hf, eval₂_zero] at h
    exact (aeval_coordClass_eq_zero P f).1 h.symm
  · obtain ⟨S, hS, rfl⟩ := hP
    rw [Ideal.span_le]
    intro g hgS
    obtain ⟨a, ha⟩ := hS g hgS
    have hgP : aeval (coordClass (Ideal.span S)) g = 0 :=
      (aeval_coordClass_eq_zero _ g).2 (Ideal.subset_span hgS)
    have hy : aeval (birPoint c hc) g = 0 := by
      apply Subtype.ext
      rw [coe_aeval_birPoint c hc ha, hgP, zero_mul]
      rfl
    show g ∈ RingHom.ker (mConeMap (birPoint c hc))
    rw [RingHom.mem_ker]
    show aeval (fun p => C (birPoint c hc p) * X p.1) g = 0
    refine (aeval_scale ha (fun p => C (birPoint c hc p)) X).trans ?_
    rw [← hom_aeval C, hy, map_zero, zero_mul]

theorem birational_birPoint (c : ∀ k, ι k) (hc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ P) :
    Birational (birPoint c hc) := by
  rintro ⟨s, d, g, h, hg, hh, h0, hs⟩
  refine ⟨d, g, h, hg, hh, ?_, ?_⟩
  · intro h'
    have := congrArg (fun t : fnField P => (t : FractionRing (MRing ι ⧸ P))) h'
    simp only [coe_aeval_birPoint c hc hh, ZeroMemClass.coe_zero] at this
    exact mul_ne_zero h0 (prod_inv_ne_zero c hc d) this
  · apply Subtype.ext
    rw [Subfield.coe_mul, coe_aeval_birPoint c hc hg, coe_aeval_birPoint c hc hh]
    show _ = s * _
    rw [hs, mul_assoc]

end BirationalModelExists

theorem BirationalModelExists.proof : BirationalModelExists.Statement := by
  intro K _ ι _ P d hP
  obtain ⟨_, ⟨hprime, hhom, hrel⟩, _, _⟩ := hP
  choose c hc using hrel
  have := hprime
  exact ⟨BirationalModelExists.fnField P, inferInstance, BirationalModelExists.birPoint c hc,
    BirationalModelExists.mCoordIdeal_birPoint hhom c hc, BirationalModelExists.birational_birPoint c hc⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
