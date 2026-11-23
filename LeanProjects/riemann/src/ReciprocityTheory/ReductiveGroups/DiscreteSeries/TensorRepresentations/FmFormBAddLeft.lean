import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.TraceFormula
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.UnitarizeC

set_option autoImplicit false

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {D : Submodule ℂ H} {ε : Fin n → Bool}

theorem fm_sgn_star (c : Fin n) : starRingEnd ℂ (if ε c then (1 : ℂ) else -1) = if ε c then 1 else -1 := by
  split_ifs <;> simp

theorem fm_formB_add_left (f f' g : Fin n → D) : formB ε (f + f') g = formB ε f g + formB ε f' g := by
  simp only [formB, Pi.add_apply, Submodule.coe_add, inner_add_left, mul_add, sum_add_distrib]

theorem fm_sum_ite_left (w : Fin n → ℂ) (a : Fin n) (x : D) (G : Fin n → D) :
    ∑ c, w c * inner ℂ (((if c = a then x else 0 : D)) : H) ((G c : D) : H) = w a * inner ℂ (x : H) ((G a : D) : H) := by
  rw [Finset.sum_eq_single a (fun c _ hc => by rw [if_neg hc]; simp) (fun h => absurd (Finset.mem_univ a) h), if_pos rfl]

theorem fm_sum_ite_right (w : Fin n → ℂ) (a : Fin n) (x : D) (G : Fin n → D) :
    ∑ c, w c * inner ℂ ((G c : D) : H) (((if c = a then x else 0 : D)) : H) = w a * inner ℂ ((G a : D) : H) (x : H) := by
  rw [Finset.sum_eq_single a (fun c _ hc => by rw [if_neg hc]; simp) (fun h => absurd (Finset.mem_univ a) h), if_pos rfl]

theorem fm_formB_tensF (dual : Bool) {E : Fin n → Fin n → Module.End ℂ D} (hU : IsInfUnitary ε E) (a b : Fin n)
    (f g : Fin n → D) :
    formB ε (tensF dual E a b f) g = adjSign ε a b * formB ε f (tensF dual E b a g) := by
  have hU' : ∀ (x y : D), inner ℂ ((E a b x : D) : H) (y : H) = adjSign ε a b * inner ℂ (x : H) ((E b a y : D) : H) := by
    intro x y; simpa only [Submodule.coe_inner] using hU a b x y
  cases dual
  · simp only [formB, tensF, cond_false, tensV_coord, Submodule.coe_add, inner_add_left, inner_add_right, hU',
      mul_add, sum_add_distrib, mul_sum]
    have h2 : ∑ i, adjSign ε a b * ((if ε i then (1 : ℂ) else -1) * inner ℂ ((f i : D) : H)
        (((if i = b then g a else 0 : D)) : H)) = adjSign ε a b * ((if ε b then (1 : ℂ) else -1) *
          inner ℂ ((f b : D) : H) ((g a : D) : H)) := by
      rw [Finset.sum_eq_single b (fun c _ hc => by rw [if_neg hc]; simp) (fun h => absurd (Finset.mem_univ b) h),
        if_pos rfl]
    rw [h2, fm_sum_ite_left, ← tfa_sign ε a b]
    congr 1
    · exact sum_congr rfl fun c _ => by ring
    · ring
  · simp only [formB, tensF, cond_true, tensVd_coord, Submodule.coe_sub, inner_sub_left, inner_sub_right, hU',
      mul_sub, sum_sub_distrib, mul_sum]
    have h2 : ∑ i, adjSign ε a b * ((if ε i then (1 : ℂ) else -1) * inner ℂ ((f i : D) : H)
        (((if i = a then g b else 0 : D)) : H)) = adjSign ε a b * ((if ε a then (1 : ℂ) else -1) *
          inner ℂ ((f a : D) : H) ((g b : D) : H)) := by
      rw [Finset.sum_eq_single a (fun c _ hc => by rw [if_neg hc]; simp) (fun h => absurd (Finset.mem_univ a) h),
        if_pos rfl]
    rw [h2, fm_sum_ite_left, ← tfa_sign' ε b a]
    congr 1
    · exact sum_congr rfl fun c _ => by ring
    · ring

end

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}

theorem fm_kset_uj {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) : k ∈ UJset ε := by
  obtain ⟨h1, -⟩ := rq_K_unit hk
  show kᴴ * Jm ε * k = Jm ε
  rw [Matrix.mul_assoc, ← hk.2, ← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem fm_JJ {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (d e : Fin n) :
    ∑ c, (if ε c then (1 : ℂ) else -1) * (star (k c d) * k c e) = if d = e then (if ε d then (1 : ℂ) else -1) else 0 := by
  have h := congrFun (congrFun (fm_kset_uj hk : kᴴ * Jm ε * k = Jm ε) d) e
  rw [Matrix.mul_apply] at h
  simp only [Jm, Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.diagonal_apply] at h
  rw [← h]
  refine sum_congr rfl fun c _ => ?_
  simp only [RCLike.star_def]
  ring

theorem fm_formBH_kDiag (dual : Bool) {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ)
    {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (F G : Fin n → H) :
    ∑ c, (if ε c then (1 : ℂ) else -1) * inner ℂ (kDiag dual σ k F c) (kDiag dual σ k G c) =
      ∑ c, (if ε c then (1 : ℂ) else -1) * inner ℂ (F c) (G c) := by
  have hin : ∀ u v : H, inner ℂ (σ k u) (σ k v) = inner ℂ u v := fun u v =>
    UnitB.sig_inner hσ (UnitB.toG k (fm_kset_uj hk)) u v
  set m : Fin n → Fin n → ℂ := fun c d => cond dual (star (k c d)) (k c d) with hm
  have hJ : ∀ d e, ∑ c, (if ε c then (1 : ℂ) else -1) * (star (m c d) * m c e) =
      if d = e then (if ε d then (1 : ℂ) else -1) else 0 := by
    intro d e
    cases dual
    · exact fm_JJ hk d e
    · have h := congrArg star (fm_JJ hk d e)
      rw [star_sum] at h
      have h2 : star (if d = e then (if ε d then (1 : ℂ) else -1) else 0) = if d = e then (if ε d then (1 : ℂ) else -1) else 0 := by
        split_ifs <;> simp
      rw [h2] at h
      rw [← h]
      refine sum_congr rfl fun c _ => ?_
      simp only [hm, cond_true, star_mul, star_star]
      split_ifs <;> simp [mul_comm]
  have hk1 : ∀ (F : Fin n → H) c, kDiag dual σ k F c = ∑ d, m c d • σ k (F d) := fun F c => rfl
  simp only [hk1, sum_inner, inner_sum, inner_smul_left, inner_smul_right, hin, mul_sum]
  have key : ∀ X : Fin n → Fin n → Fin n → ℂ, ∑ c, ∑ e, ∑ d, X c e d = ∑ d, ∑ e, ∑ c, X c e d := by
    intro X
    rw [show (∑ c, ∑ e, ∑ d, X c e d) = ∑ c, ∑ d, ∑ e, X c e d from sum_congr rfl fun c _ => sum_comm, sum_comm]
    exact sum_congr rfl fun d _ => sum_comm
  refine (key _).trans ?_
  calc _ = ∑ d, ∑ e, (if d = e then (if ε d then (1 : ℂ) else -1) else 0) * inner ℂ (F d) (G e) := by
        refine sum_congr rfl fun d _ => sum_congr rfl fun e _ => ?_
        rw [← hJ d e, sum_mul]
        refine sum_congr rfl fun c _ => ?_
        simp only [RCLike.star_def]; ring
    _ = _ := by simp only [ite_mul, zero_mul, sum_ite_eq, mem_univ, if_true]

end

end ReciprocityTheory.ChartRestriction.DS
