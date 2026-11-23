import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SignBasis

section General

variable {E M ι : Type} [Field E] [StarRing E] [AddCommGroup M] [Module E M] [Fintype ι] [DecidableEq ι]

theorem form_eq_sum (h : M →ₗ⋆[E] M →ₗ[E] E) (b : Module.Basis ι E M) (hb : ∀ i j, i ≠ j → h (b i) (b j) = 0)
    (x y : M) : h x y = ∑ i, star (b.repr x i) * b.repr y i * h (b i) (b i) := by
  conv_lhs => rw [← b.sum_repr x, ← b.sum_repr y]
  rw [map_sum h, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum, Finset.sum_eq_single i]
  · rw [LinearMap.map_smulₛₗ h, LinearMap.smul_apply, map_smul, smul_eq_mul, smul_eq_mul, starRingEnd_apply]; ring
  · intro j _ hj
    rw [LinearMap.map_smulₛₗ h, LinearMap.smul_apply, map_smul, hb i j hj.symm]; simp
  · simp

theorem re_form_eq_sum (h : M →ₗ⋆[E] M →ₗ[E] E) (b : Module.Basis ι E M) (hb : ∀ i j, i ≠ j → h (b i) (b j) = 0)
    (t : E →+* ℂ) (ht : ∀ a, t (star a) = starRingEnd ℂ (t a)) (x : M) :
    (t (h x x)).re = ∑ i, Complex.normSq (t (b.repr x i)) * (t (h (b i) (b i))).re := by
  rw [form_eq_sum h b hb, map_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_mul, ht, ← Complex.normSq_eq_conj_mul_self, Complex.re_ofReal_mul]

theorem re_ne_zero (h : M →ₗ⋆[E] M →ₗ[E] E) (hs : h.IsSymm) (hn : h.Nondegenerate) (b : Module.Basis ι E M)
    (hb : ∀ i j, i ≠ j → h (b i) (b j) = 0)
    (t : E →+* ℂ) (ht : ∀ a, t (star a) = starRingEnd ℂ (t a)) (i : ι) : (t (h (b i) (b i))).re ≠ 0 := by
  intro h0
  have h1 : starRingEnd ℂ (t (h (b i) (b i))) = t (h (b i) (b i)) := by
    rw [← ht]; exact congrArg t (hs.eq _ _)
  have h2 := Complex.conj_eq_iff_im.1 h1
  have h3 : h (b i) (b i) = 0 := t.injective (by rw [map_zero]; exact Complex.ext h0 h2)
  refine b.ne_zero i (hn.1 _ fun y => ?_)
  rw [form_eq_sum h b hb]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hj : i = j
  · rw [← hj, h3, mul_zero]
  · simp [Finsupp.single_apply, hj]

def coordSub (b : Module.Basis ι E M) (p : ι → Prop) : Submodule E M where
  carrier := {x | ∀ i, ¬ p i → b.repr x i = 0}
  zero_mem' := fun i _ => by simp
  add_mem' := fun {x y} hx hy i hi => by simp [hx i hi, hy i hi]
  smul_mem' := fun c x hx i hi => by simp [hx i hi]

theorem isCompl_coordSub (b : Module.Basis ι E M) (p : ι → Prop) :
    IsCompl (coordSub b p) (coordSub b fun i => ¬ p i) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hx'
    refine b.ext_elem fun i => ?_
    rw [map_zero, Finsupp.zero_apply]
    by_cases hi : p i
    · exact hx' i (not_not.2 hi)
    · exact hx i hi
  · rw [codisjoint_iff, eq_top_iff, ← b.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    by_cases hi : p i
    · refine Submodule.mem_sup_left (S := coordSub b p) fun j hj => ?_
      have : i ≠ j := fun e => hj (e ▸ hi)
      simp [Finsupp.single_apply, this]
    · refine Submodule.mem_sup_right (T := coordSub b fun i => ¬ p i) fun j hj => ?_
      have : i ≠ j := fun e => hj (e ▸ hi)
      simp [Finsupp.single_apply, this]

theorem sum_pos_of_coord (b : Module.Basis ι E M) (t : E →+* ℂ) (p : ι → Prop) (d : ι → ℝ) (hd : ∀ i, p i → 0 < d i)
    (x : M) (hx : x ∈ coordSub b p) (h0 : x ≠ 0) : 0 < ∑ i, Complex.normSq (t (b.repr x i)) * d i := by
  obtain ⟨j, hj⟩ : ∃ j, b.repr x j ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact h0 (b.ext_elem fun i => by simp [hc i])
  refine Finset.sum_pos' (fun i _ => ?_) ⟨j, Finset.mem_univ _, ?_⟩
  · by_cases hi : p i
    · exact mul_nonneg (Complex.normSq_nonneg _) (hd i hi).le
    · rw [hx i hi]; simp
  · refine mul_pos (Complex.normSq_pos.2 ((map_ne_zero t).2 hj)) (hd j ?_)
    by_contra hc
    exact hj (hx j hc)

theorem apply_eq_smul (b : Module.Basis ι E M) (p : ι → Prop) (s : Module.End E M) (c : E)
    (hs : ∀ i, p i → s (b i) = c • b i) (x : M) (hx : x ∈ coordSub b p) : s x = c • x := by
  conv_lhs => rw [← b.sum_repr x]
  conv_rhs => rw [← b.sum_repr x]
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : p i
  · rw [map_smul, hs i hi, smul_comm]
  · rw [hx i hi]; simp

omit [StarRing E] in
theorem mem_of_fixed [CharZero E] {P N : Submodule E M} (hc : IsCompl P N) (s : Module.End E M)
    (hP : ∀ x ∈ P, s x = x) (hN : ∀ x ∈ N, s x = -x) (x : M) (hx : s x = x) : x ∈ P := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (hc.sup_eq_top ▸ Submodule.mem_top : x ∈ P ⊔ N)
  rw [map_add, hP y hy, hN z hz, add_right_inj] at hx
  have : (2 : E) • z = 0 := by rw [two_smul]; nth_rewrite 1 [← hx]; exact neg_add_cancel z
  rw [(smul_eq_zero.1 this).resolve_left two_ne_zero, add_zero]
  exact hy

end General

theorem signInv_diag_iff : ∀ (D : D7) (V : HSp D) (b : Module.Basis (Fin V.rank) D.host.E V.V), (∀ i j, i ≠ j → V.hT (b i) (b j) = 0) → ∀ (τ : D.what₂.Tau) (s : Module.End D.host.E V.V), (IsSignInv V τ s ∧ ∀ i, s (b i) = b i ∨ s (b i) = -b i) ↔ ∀ i, s (b i) = if 0 < (tauE D τ (V.hT (b i) (b i))).re then b i else -b i := by
  intro D V b hb τ s
  have ht := tauE_star (D := D) τ
  have hne := re_ne_zero V.hT V.herm V.nondeg b hb (tauE D τ) ht
  constructor
  · rintro ⟨⟨P, N, hd, hP, hN⟩, hs⟩ i
    rcases hs i with h | h
    · rw [if_pos (hd.pos _ (mem_of_fixed hd.compl s hP hN _ h) (b.ne_zero i)), h]
    · have : b i ∈ N := mem_of_fixed hd.compl.symm (-s) (fun x hx => by rw [LinearMap.neg_apply, hN x hx, neg_neg])
        (fun x hx => by rw [LinearMap.neg_apply, hP x hx]) _ (by rw [LinearMap.neg_apply, h, neg_neg])
      rw [if_neg (hd.neg _ this (b.ne_zero i)).not_gt, h]
  · intro hs
    refine ⟨⟨coordSub b fun i => 0 < (tauE D τ (V.hT (b i) (b i))).re,
      coordSub b fun i => ¬ 0 < (tauE D τ (V.hT (b i) (b i))).re,
      ⟨isCompl_coordSub b _, fun x hx y hy => ?_, fun x hx h0 => ?_, fun x hx h0 => ?_⟩, fun x hx => ?_, fun x hx => ?_⟩,
      fun i => ?_⟩
    · rw [form_eq_sum V.hT b hb]
      refine Finset.sum_eq_zero fun i _ => ?_
      by_cases hi : 0 < (tauE D τ (V.hT (b i) (b i))).re
      · rw [hy i (not_not.2 hi), mul_zero, zero_mul]
      · rw [hx i hi, star_zero, zero_mul, zero_mul]
    · rw [re_form_eq_sum V.hT b hb _ ht]
      exact sum_pos_of_coord b _ _ _ (fun i hi => hi) x hx h0
    · rw [re_form_eq_sum V.hT b hb _ ht]
      have := sum_pos_of_coord b (tauE D τ) _ (fun i => -(tauE D τ (V.hT (b i) (b i))).re)
        (fun i hi => neg_pos.2 (lt_of_le_of_ne (not_lt.1 hi) (hne i))) x hx h0
      simp only [mul_neg, Finset.sum_neg_distrib] at this
      exact neg_pos.1 this
    · have := apply_eq_smul b _ s 1 (fun i hi => by rw [hs i, if_pos hi, one_smul]) x hx
      rwa [one_smul] at this
    · have := apply_eq_smul b _ s (-1) (fun i hi => by rw [hs i, if_neg hi, neg_one_smul]) x hx
      rwa [neg_one_smul] at this
    · rw [hs i]
      split_ifs
      · exact Or.inl rfl
      · exact Or.inr rfl

end GlobalTheory.SignBasis
