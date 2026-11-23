import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LeftPhaseRule.HasDerivAtPhase

open Matrix
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.QuantumDeterminants.WeylGroupFacts

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace Formalism.FourierDecayAlt.Q.LeftMultiplicationRule

variable {k r : ℕ}

lemma single_conj (A B : Mx k r) (a b p q : Fin (2 * r + k + 1)) :
    ((A * Matrix.single a b 1 * B : Mx k r)) p q = A p a * B b q := by
  simp only [Matrix.mul_apply, Matrix.single_apply, ite_and, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]

private lemma hpk_eq_lemma (i j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j = tau k r i then WeylGroupFacts.sgn k r i else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  unfold Hpk WeylGroupFacts.sgn
  simp only [Fin.ext_iff, tau_val]
  split_ifs <;> first | rfl | omega | norm_num

lemma hpkVec (u : Fin (2 * r + k + 1) → ℂ) (s : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ u) s = WeylGroupFacts.sgn k r s * u (tau k r s) := by
  simp only [Matrix.mulVec, dotProduct, hpk_eq_lemma, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]

lemma posL_in (l : Fin r) (j : Fin (mdim k r l.succ)) :
    l.val < (posL k r l.succ j).val ∧ (posL k r l.succ j).val < 2 * r + k - l.val := by
  have hj := j.isLt
  have hl := l.isLt
  unfold mdim at hj
  show l.val < j.val + l.succ.val ∧ j.val + l.succ.val < 2 * r + k - l.val
  simp only [Fin.val_succ] at hj ⊢
  omega

lemma fvec_es {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (l : Fin r) :
    fvec k r z l.succ (esI k r l) = 0 := by
  have hl := l.isLt
  unfold fvec
  split_ifs with h
  · simp only [bvec, Pi.single_apply]
    rw [if_neg]
    intro h'
    have h'' := congrArg Fin.val h'
    simp only [eI, esI, Fin.val_succ] at h'' h
    omega
  · apply hz
    right
    show r + k < 2 * r + k - l.val
    omega

lemma ell_form {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {l : Fin r} {M : Mx k r}
    (hM : InS k r l M) : ell k r z M = ∑ q, M (eI k r l) q * fvec k r z l.succ q := by
  have hl := l.isLt
  unfold ell
  rw [Finset.sum_eq_single l]
  · split_ifs with h
    · unfold fvec
      rw [dif_pos (show l.succ.val < r by simp only [Fin.val_succ]; exact h)]
      simp only [bvec, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rfl
    · unfold fvec
      rw [dif_neg (show ¬ l.succ.val < r by simp only [Fin.val_succ]; exact h)]
      rfl
  · intro a _ hal
    have hal' : a.val ≠ l.val := Fin.val_ne_of_ne hal
    have hal2 := a.isLt
    split_ifs with h
    · apply hM
      intro hs
      unfold SP at hs
      simp only [eI] at hs
      omega
    · simp only [Matrix.mulVec, dotProduct]
      apply Finset.sum_eq_zero
      intro q _
      have hq2 := q.isLt
      by_cases hq : r + k < q.val
      · rw [hz q (Or.inr hq), mul_zero]
      · rw [hM _ _ ?_, zero_mul]
        intro hs
        unfold SP at hs
        simp only [eI] at hs
        omega
  · intro h
    exact absurd (Finset.mem_univ l) h

private lemma tau_tau_lemma (i : Fin (2 * r + k + 1)) : tau k r (tau k r i) = i := by
  have hi := i.isLt
  apply Fin.ext
  simp only [tau_val]
  split_ifs <;> omega

private lemma sgn_tau_lemma (i : Fin (2 * r + k + 1)) : WeylGroupFacts.sgn k r (tau k r i) = WeylGroupFacts.sgn k r i := by
  have hi := i.isLt
  unfold WeylGroupFacts.sgn
  simp only [tau_val]
  split_ifs <;> first | rfl | omega

private lemma hpk_col_lemma (x y : Fin (2 * r + k + 1)) :
    Hpk k r x y = if x = tau k r y then WeylGroupFacts.sgn k r y else 0 := by
  rw [hpk_eq_lemma]
  by_cases h : x = tau k r y
  · subst h
    simp [tau_tau_lemma, sgn_tau_lemma]
  · rw [if_neg h, if_neg]
    intro h'
    apply h
    rw [h', tau_tau_lemma]

private lemma hpk_mul_conjTranspose_mul_hpk_apply (M : Mx k r) (p q : Fin (2 * r + k + 1)) :
    (Hpk k r * Mᴴ * Hpk k r) p q =
      WeylGroupFacts.sgn k r p * star (M (tau k r q) (tau k r p)) * WeylGroupFacts.sgn k r q := by
  rw [Matrix.mul_apply]
  have inner : ∀ y, (Hpk k r * Mᴴ) p y = WeylGroupFacts.sgn k r p * star (M y (tau k r p)) := fun y => by
    rw [Matrix.mul_apply]
    simp only [hpk_eq_lemma, Matrix.conjTranspose_apply, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [inner, hpk_col_lemma, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]

private lemma sp_of_sp_tau {l : Fin r} {p q : Fin (2 * r + k + 1)}
    (h : SP k r l (tau k r q) (tau k r p)) : SP k r l p q := by
  have hl := l.isLt
  have hp := p.isLt
  have hq := q.isLt
  have e1 := tau_val (k := k) (r := r) p
  have e2 := tau_val (k := k) (r := r) q
  unfold SP at h ⊢
  split_ifs at e1 e2 <;> omega

lemma ell_dag_form {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {l : Fin r} {M : Mx k r}
    (hM : InS k r l M) : ell k r z (Hpk k r * Mᴴ * Hpk k r) =
      ∑ q, star (M (tau k r q) (esI k r l)) * WeylGroupFacts.sgn k r q * fvec k r z l.succ q := by
  have hN : InS k r l (Hpk k r * Mᴴ * Hpk k r) := by
    intro p q hpq
    rw [hpk_mul_conjTranspose_mul_hpk_apply, hM _ _ (fun h => hpq (sp_of_sp_tau h)), star_zero, mul_zero, zero_mul]
  rw [ell_form hz hN]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [hpk_mul_conjTranspose_mul_hpk_apply, tau_e, sgn_e, one_mul]

section Cases

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {z : Fin (2 * r + k + 1) → ℂ}
  {l : Fin r} {D : Set (Mx k r)} {f : Mx k r → E} {c : ℂ} {g₁ : Mx k r}

lemma ginv_eq (hc : c ≠ 0) : (w1 k r l c * g₁)⁻¹ = g₁⁻¹ * w1 k r l (star c) := by
  rw [Matrix.mul_inv_rev, weyl_cell_inv l c hc]

lemma e_out (l : Fin r) : ¬ (l.val < (eI k r l).val ∧ (eI k r l).val < 2 * r + k - l.val) := by
  intro h
  exact absurd h.1 (lt_irrefl _)

lemma es_out (l : Fin r) : ¬ (l.val < (esI k r l).val ∧ (esI k r l).val < 2 * r + k - l.val) := by
  intro h
  exact absurd h.2 (lt_irrefl _)

lemma case1 (hz : inWb k r z) (hL : LeftEq k r z l.castSucc D f) (hc : c ≠ 0)
    (hg₁ : g₁ ∈ Glev k r l.succ) (hgD : w1 k r l c * g₁ ∈ D) (v : Fin (2 * r + k + 1))
    (hv : l.val < v.val ∧ v.val < 2 * r + k - l.val) :
    EH k r v (eI k r l) f (w1 k r l c * g₁) =
      (c⁻¹ * herm (Hpk k r) (g₁ *ᵥ bvec v) (fvec k r z l.succ)) • f (w1 k r l c * g₁) := by
  have hl := l.isLt
  have hg : w1 k r l c * g₁ ∈ Glev k r l.castSucc ∩ D := ⟨wg_glev l c hc hg₁, hgD⟩
  have hinv := glev_inv hg₁
  have hv1 : v ≠ eI k r l := fun h => by rw [h] at hv; exact e_out l hv
  have hv2 : v ≠ esI k r l := fun h => by rw [h] at hv; exact es_out l hv
  have hre := (glev_out hg₁ (eI k r l) (e_out l)).1
  have hres := (glev_out hg₁ (esI k r l) (es_out l)).1
  have h0e : g₁ (eI k r l) v = 0 := by rw [hre, if_neg (Ne.symm hv1)]
  have h0es : g₁ (esI k r l) v = 0 := by rw [hres, if_neg (Ne.symm hv2)]
  have hcol : ∀ p, (w1 k r l c * g₁) p v = g₁ p v := fun p => weyl_cell_mul_apply l c g₁ p v h0e h0es
  have hire := (glev_out hinv (eI k r l) (e_out l)).1
  have hB : ∀ q, (g₁⁻¹ * w1 k r l (star c)) (eI k r l) q = if q = esI k r l then c⁻¹ else 0 :=
    fun q => by
      rw [Matrix.mul_apply]
      simp only [hire, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [weyl_cell_apply_basis, star_star]
  have hMe : ∀ p q, (w1 k r l c * g₁ * Matrix.single v (eI k r l) 1 * (w1 k r l c * g₁)⁻¹ : Mx k r) p q =
      g₁ p v * (if q = esI k r l then c⁻¹ else 0) := fun p q => by
    rw [ginv_eq hc, single_conj, hcol, hB]
  have hS : InS k r l (w1 k r l c * g₁ * Matrix.single v (eI k r l) 1 * (w1 k r l c * g₁)⁻¹) := by
    intro p q hpq
    rw [hMe]
    by_cases hq : q = esI k r l
    · have hp : ¬ (l.val < p.val ∧ p.val < 2 * r + k - l.val) :=
        fun hp => hpq (Or.inr ⟨by rw [hq]; rfl, hp.1, hp.2⟩)
      rw [(glev_out hg₁ p hp).1 v, if_neg (fun (h : p = v) => hp (h ▸ hv)), zero_mul]
    · rw [if_neg hq, mul_zero]
  rw [core hz hL hg v (eI k r l) hS, ell_form hz hS, ell_dag_form hz hS]
  congr 1
  simp only [hMe, h0e, zero_mul, Finset.sum_const_zero, zero_add, eq_self_iff_true, if_true]
  unfold herm
  simp only [dotProduct, Pi.star_apply]
  simp only [hpkVec]
  simp only [Matrix.mulVec, dotProduct, bvec, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [star_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [star_mul', star_star, star_sgn]
  ring

lemma case2 (hz : inWb k r z) (hL : LeftEq k r z l.castSucc D f) (hc : c ≠ 0)
    (hg₁ : g₁ ∈ Glev k r l.succ) (hgD : w1 k r l c * g₁ ∈ D) (v : Fin (2 * r + k + 1))
    (hv : l.val < v.val ∧ v.val < 2 * r + k - l.val) :
    EH k r (esI k r l) v f (w1 k r l c * g₁) =
      ((star c)⁻¹ * (g₁⁻¹ *ᵥ fvec k r z l.succ) v) • f (w1 k r l c * g₁) := by
  have hl := l.isLt
  have hg : w1 k r l c * g₁ ∈ Glev k r l.castSucc ∩ D := ⟨wg_glev l c hc hg₁, hgD⟩
  have hinv := glev_inv hg₁
  have hv1 : v ≠ eI k r l := fun h => by rw [h] at hv; exact e_out l hv
  have hv2 : v ≠ esI k r l := fun h => by rw [h] at hv; exact es_out l hv
  have hces := (glev_out hg₁ (esI k r l) (es_out l)).2
  have hice := (glev_out hinv (eI k r l) (e_out l)).2
  have hices := (glev_out hinv (esI k r l) (es_out l)).2
  have hA : ∀ p, (w1 k r l c * g₁) p (esI k r l) = if p = eI k r l then (star c)⁻¹ else 0 :=
    fun p => by
      rw [Matrix.mul_apply]
      simp only [hces, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [reflection_column_dual_isotropic]
  have h0 : g₁⁻¹ v (esI k r l) = 0 := by rw [hices, if_neg hv2]
  have hB : ∀ q, (g₁⁻¹ * w1 k r l (star c)) v q = g₁⁻¹ v q := fun q =>
    mul_weyl_cell_apply l (star c) g₁⁻¹ v q (by rw [hice, if_neg hv1]) h0
  have hMe : ∀ p q, (w1 k r l c * g₁ * Matrix.single (esI k r l) v 1 * (w1 k r l c * g₁)⁻¹ : Mx k r) p q =
      (if p = eI k r l then (star c)⁻¹ else 0) * g₁⁻¹ v q := fun p q => by
    rw [ginv_eq hc, single_conj, hA, hB]
  have hS : InS k r l (w1 k r l c * g₁ * Matrix.single (esI k r l) v 1 * (w1 k r l c * g₁)⁻¹) := by
    intro p q hpq
    rw [hMe]
    by_cases hp : p = eI k r l
    · have hq : ¬ (l.val < q.val ∧ q.val < 2 * r + k - l.val) :=
        fun hq => hpq (Or.inl ⟨by rw [hp]; rfl, hq.1, le_of_lt hq.2⟩)
      rw [(glev_out hinv q hq).2 v, if_neg (fun (h : v = q) => hq (h ▸ hv)), mul_zero]
    · rw [if_neg hp, zero_mul]
  rw [core hz hL hg (esI k r l) v hS, ell_form hz hS, ell_dag_form hz hS]
  congr 1
  simp only [hMe, h0, mul_zero, star_zero, zero_mul, Finset.sum_const_zero, add_zero, eq_self_iff_true,
    if_true]
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  ring

lemma case3 (hz : inWb k r z) (hL : LeftEq k r z l.castSucc D f) (hc : c ≠ 0)
    (hg₁ : g₁ ∈ Glev k r l.succ) (hgD : w1 k r l c * g₁ ∈ D) :
    EH k r (esI k r l) (eI k r l) f (w1 k r l c * g₁) = 0 := by
  have hl := l.isLt
  have hg : w1 k r l c * g₁ ∈ Glev k r l.castSucc ∩ D := ⟨wg_glev l c hc hg₁, hgD⟩
  have hinv := glev_inv hg₁
  have hre := (glev_out hg₁ (eI k r l) (e_out l)).1
  have hces := (glev_out hg₁ (esI k r l) (es_out l)).2
  have hire := (glev_out hinv (eI k r l) (e_out l)).1
  have hA : ∀ p, (w1 k r l c * g₁) p (esI k r l) = if p = eI k r l then (star c)⁻¹ else 0 :=
    fun p => by
      rw [Matrix.mul_apply]
      simp only [hces, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [reflection_column_dual_isotropic]
  have hB : ∀ q, (g₁⁻¹ * w1 k r l (star c)) (eI k r l) q = if q = esI k r l then c⁻¹ else 0 :=
    fun q => by
      rw [Matrix.mul_apply]
      simp only [hire, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [weyl_cell_apply_basis, star_star]
  have hMe : ∀ p q,
      (w1 k r l c * g₁ * Matrix.single (esI k r l) (eI k r l) 1 * (w1 k r l c * g₁)⁻¹ : Mx k r) p q =
      (if p = eI k r l then (star c)⁻¹ else 0) * (if q = esI k r l then c⁻¹ else 0) := fun p q => by
    rw [ginv_eq hc, single_conj, hA, hB]
  have hS : InS k r l
      (w1 k r l c * g₁ * Matrix.single (esI k r l) (eI k r l) 1 * (w1 k r l c * g₁)⁻¹) := by
    intro p q hpq
    rw [hMe]
    by_cases hp : p = eI k r l
    · by_cases hq : q = esI k r l
      · exfalso
        apply hpq
        left
        subst hp
        subst hq
        exact ⟨rfl, show l.val < 2 * r + k - l.val by omega, le_refl _⟩
      · rw [if_neg hq, mul_zero]
    · rw [if_neg hp, zero_mul]
  rw [core hz hL hg (esI k r l) (eI k r l) hS, ell_form hz hS, ell_dag_form hz hS]
  have h1 : ∑ q, (w1 k r l c * g₁ * Matrix.single (esI k r l) (eI k r l) 1 * (w1 k r l c * g₁)⁻¹ : Mx k r)
      (eI k r l) q * fvec k r z l.succ q = 0 := by
    apply Finset.sum_eq_zero
    intro q _
    rw [hMe, if_pos rfl]
    by_cases hq : q = esI k r l
    · rw [hq, fvec_es hz l, mul_zero]
    · rw [if_neg hq, mul_zero, zero_mul]
  have h2 : ∑ q, star ((w1 k r l c * g₁ * Matrix.single (esI k r l) (eI k r l) 1 *
      (w1 k r l c * g₁)⁻¹ : Mx k r) (tau k r q) (esI k r l)) * WeylGroupFacts.sgn k r q * fvec k r z l.succ q = 0 := by
    apply Finset.sum_eq_zero
    intro q _
    by_cases hq : q = esI k r l
    · rw [hq, fvec_es hz l, mul_zero]
    · rw [hMe, if_neg (fun h => hq (by rw [← tau_tau_lemma q, h, tau_e])), zero_mul, star_zero,
        zero_mul, zero_mul]
  rw [h1, h2, star_zero, add_zero, zero_smul]

end Cases

theorem left_multiplication_rule : RuleLeft := by
  intro E _ _ k r z l D f hz _ _ _ hL c hc g₁ hg₁ hgD
  refine ⟨fun j => ?_, fun j => ?_, case3 hz hL hc hg₁ hgD⟩
  · exact case1 hz hL hc hg₁ hgD _ (posL_in l j)
  · exact case2 hz hL hc hg₁ hgD _ (posL_in l j)

end Formalism.FourierDecayAlt.Q.LeftMultiplicationRule
