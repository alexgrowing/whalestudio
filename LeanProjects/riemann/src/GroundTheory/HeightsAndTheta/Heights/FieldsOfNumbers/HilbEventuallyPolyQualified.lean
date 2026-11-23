import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

namespace HilbEventuallyPoly

section Lemmas

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {F : Type*} [Field F]

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem isMultiHomogIdeal_iff_isHomogeneous (I : Ideal (MRing ι F)) :
    IsMultiHomogIdeal I ↔ I.IsHomogeneous (weightedHomogeneousSubmodule F (blockWeight ι)) := by
  constructor
  · intro h b f hf
    have key : (DirectSum.decompose (weightedHomogeneousSubmodule F (blockWeight ι)) f b :
        MRing ι F) = weightedHomogeneousComponent (blockWeight ι) b f :=
      weightedDecomposition.decompose'_apply F (blockWeight ι) f b
    rw [key]
    exact h f hf b
  · intro h f hf b
    exact weightedHomogeneousComponent_mem_of_mem F (blockWeight ι) h hf b

omit [Fintype K] in

theorem isMultiHomog_X (v : Σ k, ι k) :
    IsMultiHomog (X v : MRing ι F) (Pi.single v.1 1) :=
  isWeightedHomogeneous_X F (blockWeight ι) v

theorem weightedHomogeneousComponent_mul_X (f : MRing ι F) (b : K → ℕ) (v : Σ k, ι k) :
    weightedHomogeneousComponent (blockWeight ι) (b + blockWeight ι v) (f * X v) =
      weightedHomogeneousComponent (blockWeight ι) b f * X v := by
  have h := DirectSum.coe_decompose_mul_add_of_right_mem
    (weightedHomogeneousSubmodule F (blockWeight ι)) (a := f) (i := b)
    (isWeightedHomogeneous_X F (blockWeight ι) v)
  have key : ∀ (φ : MRing ι F) (c : K → ℕ),
      (DirectSum.decompose (weightedHomogeneousSubmodule F (blockWeight ι)) φ c : MRing ι F) =
        weightedHomogeneousComponent (blockWeight ι) c φ :=
    fun φ c => weightedDecomposition.decompose'_apply F (blockWeight ι) φ c
  rw [key, key] at h
  exact h

theorem isMultiHomogIdeal_colon_X {I : Ideal (MRing ι F)} (hI : IsMultiHomogIdeal I)
    (v : Σ k, ι k) : IsMultiHomogIdeal (I.colon (Ideal.span {(X v : MRing ι F)})) := by
  intro f hf b
  rw [Submodule.mem_colon_span_singleton, smul_eq_mul] at hf ⊢
  rw [← weightedHomogeneousComponent_mul_X]
  exact hI _ hf _

theorem isMultiHomogIdeal_sup_span {I : Ideal (MRing ι F)} (hI : IsMultiHomogIdeal I)
    {s : MRing ι F} {c : K → ℕ} (hs : IsMultiHomog s c) :
    IsMultiHomogIdeal (I ⊔ Ideal.span {s}) := by
  rw [isMultiHomogIdeal_iff_isHomogeneous] at hI ⊢
  refine hI.sup (Ideal.homogeneous_span _ _ ?_)
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  exact ⟨c, hs⟩

theorem hilbFn_eq_zero_of_block {I : Ideal (MRing ι F)} (k : K)
    (hk : ∀ i, (X ⟨k, i⟩ : MRing ι F) ∈ I) (m : K → ℤ) (hm : 1 ≤ m k) : hilbFn I m = 0 := by
  unfold hilbFn
  split_ifs with h
  · have hbot : gradedPiece I (fun k => (m k).toNat) = ⊥ := by
      rw [gradedPiece, eq_bot_iff, Submodule.map_le_iff_le_comap]
      intro f hf
      rw [Submodule.mem_comap, Submodule.mem_bot, AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk,
        Ideal.Quotient.eq_zero_iff_mem]
      rw [mem_weightedHomogeneousSubmodule] at hf
      rw [f.as_sum]
      refine Ideal.sum_mem _ fun d hd => ?_
      have hw := hf (mem_support_iff.mp hd)
      obtain ⟨i, hi⟩ : ∃ i, d ⟨k, i⟩ ≠ 0 := by
        by_contra hcon
        simp only [not_exists, ne_eq, not_not] at hcon
        have h0 : Finsupp.weight (blockWeight ι) d k = 0 := by
          rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
          refine Finset.sum_eq_zero fun v _ => ?_
          obtain ⟨k', i'⟩ := v
          simp only [blockWeight, Pi.smul_apply, smul_eq_mul]
          by_cases hkk : k' = k
          · subst hkk
            simp [hcon i']
          · simp [Ne.symm hkk]
        rw [hw] at h0
        simp only at h0
        omega
      have hmono : monomial d (coeff d f) =
          X ⟨k, i⟩ * monomial (d - Finsupp.single ⟨k, i⟩ 1) (coeff d f) := by
        rw [X, monomial_mul, one_mul, add_tsub_cancel_of_le]
        rw [Finsupp.single_le_iff]
        omega
      rw [hmono]
      exact Ideal.mul_mem_right _ _ (hk i)
    rw [hbot, finrank_bot]
    simp
  · rfl

omit [Fintype K] [DecidableEq K] in

theorem eventually_sub {P : (K → ℤ) → Prop} (h : ∀ᶠ m in Filter.atTop, P m) (e : K → ℤ) :
    ∀ᶠ m in Filter.atTop, P (m - e) := by
  rw [Filter.eventually_atTop] at h ⊢
  obtain ⟨a, ha⟩ := h
  refine ⟨a + e, fun b hb => ha _ fun k => ?_⟩
  have := hb k
  simp only [Pi.add_apply] at this
  simp only [Pi.sub_apply]
  linarith

omit [Fintype K] [DecidableEq K] in

theorem eval_shift (p : MvPolynomial K ℚ) (e m : K → ℤ) :
    eval (fun k => ((m - e) k : ℚ)) p =
      eval (fun k => (m k : ℚ)) (bind₁ (fun j => X j - C ((e j : ℤ) : ℚ)) p) := by
  have hb : ∀ (x : K → ℚ) (g : K → MvPolynomial K ℚ),
      eval x (bind₁ g p) = eval (fun j => eval x (g j)) p :=
    fun x g => eval₂Hom_bind₁ _ _ _ _
  rw [hb]
  refine congrArg (fun x => eval x p) (funext fun j => ?_)
  simp

omit [Fintype K] in

theorem cast_single (k : K) :
    (fun k' => (((Pi.single k 1 : K → ℕ) k' : ℕ) : ℤ)) = Pi.single k 1 := by
  funext k'
  by_cases h : k' = k
  · subst h; simp
  · simp [h]

end Lemmas

end HilbEventuallyPoly

theorem HilbEventuallyPoly.of_exactDivide_polyOfDiffs (h1 : HilbExactDivide.Statement.{u})
    (h2 : PolyOfDiffs.Statement) : HilbEventuallyPoly.Statement.{u} := by
  intro F _ K _ _ ι _ I hI
  refine IsNoetherian.induction
    (P := fun J : Ideal (MRing ι F) => IsMultiHomogIdeal J → ∃ p, EventuallyPoly (hilbFn J) p)
    (fun J ih hJ => ?_) I hI
  by_cases hA : ∃ v : Σ k, ι k, (X v : MRing ι F) ∉ J ∧
      J.colon (Ideal.span {(X v : MRing ι F)}) ≠ J
  ·
    obtain ⟨v, hvJ, hne⟩ := hA
    have hle : J ≤ J.colon (Ideal.span {(X v : MRing ι F)}) := fun f hf => by
      rw [Submodule.mem_colon_span_singleton, smul_eq_mul]
      exact Ideal.mul_mem_right _ J hf
    have hlt2 : J < J ⊔ Ideal.span {(X v : MRing ι F)} :=
      lt_of_le_of_ne le_sup_left fun h =>
        hvJ (h ▸ Ideal.mem_sup_right (Ideal.subset_span rfl))
    obtain ⟨p1, hp1⟩ := ih _ (lt_of_le_of_ne hle (Ne.symm hne)) (isMultiHomogIdeal_colon_X hJ v)
    obtain ⟨p2, hp2⟩ := ih _ hlt2 (isMultiHomogIdeal_sup_span hJ (isMultiHomog_X v))
    have hex := h1 F K ι J hJ _ (X v) (isMultiHomog_X v)
    rw [cast_single] at hex
    refine ⟨bind₁ (fun j => X j - C (((Pi.single v.1 1 : K → ℤ) j : ℤ) : ℚ)) p1 + p2, ?_⟩
    filter_upwards [eventually_sub hp1 (Pi.single v.1 1), hp2] with m hm1 hm2
    have hz := hex m
    rw [map_add, ← eval_shift, ← hm1, ← hm2]
    have hz' : hilbFn J m = hilbFn (J.colon (Ideal.span {(X v : MRing ι F)})) (m - Pi.single v.1 1)
        + hilbFn (J ⊔ Ideal.span {(X v : MRing ι F)}) m := by linarith
    rw [hz']
    push_cast
    rfl
  ·
    have hA' : ∀ v : Σ k, ι k, (X v : MRing ι F) ∉ J →
        J.colon (Ideal.span {(X v : MRing ι F)}) = J := fun v hv => by
      by_contra hne
      exact hA ⟨v, hv, hne⟩
    have hdiff : ∀ k, ∃ q : MvPolynomial K ℚ,
        EventuallyPoly (diffStep (Pi.single k 1) (hilbFn J)) q := by
      intro k
      by_cases hk : ∃ i, (X ⟨k, i⟩ : MRing ι F) ∉ J
      · obtain ⟨i, hi⟩ := hk
        have hlt : J < J ⊔ Ideal.span {(X ⟨k, i⟩ : MRing ι F)} :=
          lt_of_le_of_ne le_sup_left fun h =>
            hi (h ▸ Ideal.mem_sup_right (Ideal.subset_span rfl))
        obtain ⟨q, hq⟩ := ih _ hlt (isMultiHomogIdeal_sup_span hJ (isMultiHomog_X ⟨k, i⟩))
        refine ⟨q, ?_⟩
        have hex := h1 F K ι J hJ _ (X ⟨k, i⟩) (isMultiHomog_X ⟨k, i⟩)
        rw [cast_single, hA' _ hi] at hex
        filter_upwards [hq] with m hm
        rw [← hm]
        unfold diffStep
        rw [hex m]
      · simp only [not_exists, not_not] at hk
        refine ⟨0, ?_⟩
        rw [EventuallyPoly, Filter.eventually_atTop]
        refine ⟨Pi.single k 2, fun m hm => ?_⟩
        have hmk : 2 ≤ m k := by simpa using hm k
        unfold diffStep
        rw [hilbFn_eq_zero_of_block k hk m (by omega),
          hilbFn_eq_zero_of_block k hk _ (by simp only [Pi.sub_apply, Pi.single_eq_same]; omega)]
        simp
    choose q hq using hdiff
    obtain ⟨p, -, hp⟩ := h2 K (hilbFn J) (Finset.univ.sup fun k => (q k).totalDegree + 1)
      fun k => ⟨q k, Or.inr (Nat.lt_of_lt_of_le (Nat.lt_succ_self _)
        (Finset.le_sup (f := fun k => (q k).totalDegree + 1) (Finset.mem_univ k))), hq k⟩
    exact ⟨p, hp⟩

end

end GroundTheory.Heights₂.Heights.FieldNumbers
