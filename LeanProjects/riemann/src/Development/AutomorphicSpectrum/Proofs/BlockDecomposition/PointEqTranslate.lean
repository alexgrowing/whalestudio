import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsFieldIdemOne
open MeasureTheory Topology Filter GlobalTheory.CompanionTheory.NullFr
open scoped NNReal ENNReal Matrix

namespace GlobalTheory.CompanionTheory.NullFr.CoverStep

variable {A : Type} [CommRing A] {a r t : ℕ}

private theorem yc_sub_mul_mul_mul_eq (e : A)
    (P : GlobalTheory.CompanionTheory.NullFr.Fx A a r → GlobalTheory.CompanionTheory.NullFr.Fx A r a)
    (z : GlobalTheory.CompanionTheory.NullFr.Fx A a r × GlobalTheory.CompanionTheory.NullFr.Fx A a t) (hP : P z.1 * z.1 = e • 1)
    (Y₀ : GlobalTheory.CompanionTheory.NullFr.Fx A r t) (hY₀ : e • Y₀ = Y₀) (S D : GlobalTheory.CompanionTheory.NullFr.Fx A t t) :
    GlobalTheory.CompanionTheory.NullFr.yc P (z.1, (z.2 - z.1 * Y₀) * S * D) =
      (GlobalTheory.CompanionTheory.NullFr.yc P z - Y₀) * S * D := by
  simp only [GlobalTheory.CompanionTheory.NullFr.yc]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_sub, ← Matrix.mul_assoc, hP,
    Matrix.smul_mul, Matrix.one_mul, hY₀]

private theorem vc_sub_mul_mul_mul_eq (e : A)
    (P : GlobalTheory.CompanionTheory.NullFr.Fx A a r → GlobalTheory.CompanionTheory.NullFr.Fx A r a)
    (z : GlobalTheory.CompanionTheory.NullFr.Fx A a r × GlobalTheory.CompanionTheory.NullFr.Fx A a t) (hP : P z.1 * z.1 = e • 1)
    (Y₀ : GlobalTheory.CompanionTheory.NullFr.Fx A r t) (hY₀ : e • Y₀ = Y₀) (S D : GlobalTheory.CompanionTheory.NullFr.Fx A t t) :
    GlobalTheory.CompanionTheory.NullFr.vc P (z.1, (z.2 - z.1 * Y₀) * S * D) = GlobalTheory.CompanionTheory.NullFr.vc P z * S * D := by
  simp only [GlobalTheory.CompanionTheory.NullFr.vc]
  rw [yc_sub_mul_mul_mul_eq e P z hP Y₀ hY₀ S D, ← Matrix.mul_assoc z.1,
    ← Matrix.mul_assoc z.1, ← Matrix.sub_mul, ← Matrix.sub_mul, Matrix.mul_sub z.1,
    sub_sub_sub_cancel_right]

theorem mul_gU_apply' {m : ℕ} (M : Fx A m t) (i : Fin t) (d : Fin t → A) (p : Fin m) (j : Fin t) :
    (M * gU i d) p j = M p j + if j = i then ∑ k, d k * M p k else 0 := by
  rw [GlobalTheory.CompanionTheory.NullFr.gU, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, Matrix.mul_apply]
  congr 1
  by_cases h : j = i
  · rw [if_pos h]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.of_apply, if_pos h, mul_comm]
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [Matrix.of_apply, if_neg h, mul_zero]

theorem mul_gD_apply' {m : ℕ} (M : Fx A m t) (i : Fin t) (u : A) (p : Fin m) (j : Fin t) :
    (M * gD i u) p j = if j = i then u * M p i else M p j := by
  rw [GlobalTheory.CompanionTheory.NullFr.gD, Matrix.mul_diagonal]
  by_cases h : j = i
  · subst h
    simp [mul_comm]
  · simp [h, Function.update_apply]

theorem mul_gU_gD_apply {m : ℕ} (M : Fx A m t) (i : Fin t) (c : Fin t → A) (u' : A) (p : Fin m)
    (j : Fin t) :
    (M * gU i (-c) * gD i u') p j =
      if j = i then u' * (M p i - ∑ k, c k * M p k) else M p j := by
  rw [GlobalTheory.CompanionTheory.NullFr.CoverStep.mul_gD_apply', GlobalTheory.CompanionTheory.NullFr.CoverStep.mul_gU_apply', GlobalTheory.CompanionTheory.NullFr.CoverStep.mul_gU_apply']
  by_cases h : j = i
  · rw [if_pos h, if_pos h, if_pos rfl]
    simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, sub_eq_add_neg]
  · simp only [if_neg h, add_zero]

theorem gU_neg_mul (i : Fin t) (c : Fin t → A) (hc : c i = 0) : gU i (-c) * gU i c = 1 := by
  refine Matrix.ext fun p j => ?_
  rw [GlobalTheory.CompanionTheory.NullFr.CoverStep.mul_gU_apply']
  by_cases h : j = i
  · subst h
    simp [GlobalTheory.CompanionTheory.NullFr.gU, Matrix.one_apply, mul_add, Finset.sum_add_distrib, mul_ite,
      Finset.sum_ite_eq, Finset.sum_ite_eq', hc]
  · simp [GlobalTheory.CompanionTheory.NullFr.gU, h]

theorem gD_mul (i : Fin t) (u' u : A) (h : u' * u = 1) : gD i u' * gD i u = 1 := by
  refine Matrix.ext fun p q => ?_
  rw [GlobalTheory.CompanionTheory.NullFr.gD, GlobalTheory.CompanionTheory.NullFr.gD, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply,
    Matrix.one_apply]
  by_cases hpq : p = q
  · subst hpq
    by_cases hpi : p = i
    · subst hpi
      simp [h]
    · simp [Function.update_apply, hpi]
  · simp [hpq]

end GlobalTheory.CompanionTheory.NullFr.CoverStep

namespace GlobalTheory.CompanionTheory.NullFr.CoverStep

theorem point_eq_translate : ∀ {A : Type} [CommRing A] {a r t : ℕ} (e f : A) (_ : e * e = e) (_ : f * e = f) (_ : f * f = f) (P : Fx A a r → Fx A r a)
    (i : Fin t) (C : Set A) (z : Fx A a r × Fx A a t) (_ : z ∈ admitted e P) (_ : ∀ p q, z.1 p q ∈ C)
    (_ : ∀ l k, f * yc P z l k ∈ C ∧ (1 - f) * yc P z l k ∈ C)
    (_ : ∀ p k, k ≠ i → vc P z p k ∈ C) (_ : ∀ p, (1 - f) * vc P z p i ∈ C)
    (c : Fin t → A) (_ : c i = 0) (_ : ∀ k, f * c k = c k) (_ : ∀ p, f * vc P z p i = ∑ k, c k * vc P z p k)
    (u : Aˣ) (_ : (1 - f) * (u : A) = 1 - f)
    (c₀ c₁ : Fin t → A) (_ : c₀ i = 0) (_ : ∀ k, f * c₀ k = c₀ k) (_ : c₁ i = 0)
    (_ : ∀ k, f * c₁ k = c₁ k ∧ c₁ k ∈ C) (_ : ∀ k, c k = c₀ k + u * c₁ k)
    (y₀ y₁ : Fin r → A) (_ : ∀ l, f * y₀ l = y₀ l) (_ : ∀ l, f * y₁ l = y₁ l ∧ y₁ l ∈ C)
    (_ : ∀ l, f * yc P z l i - ∑ k, c₀ k * yc P z l k = y₀ l + u * y₁ l),
    ∃ w ∈ Piece e f P i C, z = (w.1, w.2 * gD i (u : A) * gU i c₀ + w.1 * yU i y₀) := by
  intro A _ a r t e f he hfe hff P i C z hz hz1 hY hKo hKi c hci hfc hfK u hu c₀ c₁ hc₀i hfc₀
    hc₁i hc₁ hc y₀ y₁ hfy₀ hy₁ hy
  simp only [GlobalTheory.CompanionTheory.NullFr.admitted, Set.mem_setOf_eq] at hz
  obtain ⟨hez1, hez2, hP⟩ := hz
  have hey₀ : ∀ l, e * y₀ l = y₀ l := fun l => by
    rw [← hfy₀ l, ← mul_assoc, mul_comm e f, hfe]
  have hY₀ : e • GlobalTheory.CompanionTheory.NullFr.yU i y₀ = GlobalTheory.CompanionTheory.NullFr.yU i y₀ := by
    refine Matrix.ext fun l j => ?_
    simp only [GlobalTheory.CompanionTheory.NullFr.yU, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    split_ifs
    · exact hey₀ l
    · exact mul_zero e
  have hY₀i : ∀ l, GlobalTheory.CompanionTheory.NullFr.yU i y₀ l i = y₀ l := fun l => by
    simp [GlobalTheory.CompanionTheory.NullFr.yU]
  have hu' : (1 - f) * ((u⁻¹ : Aˣ) : A) = 1 - f := by
    conv_lhs => rw [← hu]
    rw [mul_assoc, Units.mul_inv, mul_one]
  have h1fc₀ : ∀ k, (1 - f) * c₀ k = 0 := fun k => by
    rw [sub_mul, one_mul, hfc₀, sub_self]
  have h1fy₀ : ∀ l, (1 - f) * y₀ l = 0 := fun l => by
    rw [sub_mul, one_mul, hfy₀, sub_self]
  have hsum : ∀ l, ∑ k, c₀ k * (GlobalTheory.CompanionTheory.NullFr.yc P z - GlobalTheory.CompanionTheory.NullFr.yU i y₀) l k =
      ∑ k, c₀ k * GlobalTheory.CompanionTheory.NullFr.yc P z l k := by
    intro l
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : k = i
    · simp [hk, hc₀i]
    · simp [GlobalTheory.CompanionTheory.NullFr.yU, hk]
  have key : ∀ l, f * (GlobalTheory.CompanionTheory.NullFr.yc P z l i - y₀ l - ∑ k, c₀ k * GlobalTheory.CompanionTheory.NullFr.yc P z l k) =
      (u : A) * y₁ l := by
    intro l
    rw [mul_sub, mul_sub, hfy₀, Finset.mul_sum]
    simp_rw [← mul_assoc, hfc₀]
    rw [sub_right_comm, hy l, add_sub_cancel_left]
  have key2 : ∀ l, (1 - f) * (GlobalTheory.CompanionTheory.NullFr.yc P z l i - y₀ l -
      ∑ k, c₀ k * GlobalTheory.CompanionTheory.NullFr.yc P z l k) = (1 - f) * GlobalTheory.CompanionTheory.NullFr.yc P z l i := by
    intro l
    rw [mul_sub, mul_sub, h1fy₀, Finset.mul_sum]
    simp_rw [← mul_assoc, h1fc₀, zero_mul, Finset.sum_const_zero, sub_zero]
  have hD : GlobalTheory.CompanionTheory.NullFr.gD i ((u⁻¹ : Aˣ) : A) * GlobalTheory.CompanionTheory.NullFr.gD i (u : A) = 1 :=
    GlobalTheory.CompanionTheory.NullFr.CoverStep.gD_mul i _ _ u.inv_mul
  have hS : GlobalTheory.CompanionTheory.NullFr.gU i (-c₀) * GlobalTheory.CompanionTheory.NullFr.gU i c₀ = 1 :=
    GlobalTheory.CompanionTheory.NullFr.CoverStep.gU_neg_mul i c₀ hc₀i
  have hco := yc_sub_mul_mul_mul_eq e P z hP _ hY₀ (GlobalTheory.CompanionTheory.NullFr.gU i (-c₀))
    (GlobalTheory.CompanionTheory.NullFr.gD i ((u⁻¹ : Aˣ) : A))
  have hcm := vc_sub_mul_mul_mul_eq e P z hP _ hY₀ (GlobalTheory.CompanionTheory.NullFr.gU i (-c₀))
    (GlobalTheory.CompanionTheory.NullFr.gD i ((u⁻¹ : Aˣ) : A))
  refine ⟨(z.1, (z.2 - z.1 * GlobalTheory.CompanionTheory.NullFr.yU i y₀) * GlobalTheory.CompanionTheory.NullFr.gU i (-c₀) *
    GlobalTheory.CompanionTheory.NullFr.gD i ((u⁻¹ : Aˣ) : A)), ?_, ?_⟩
  · simp only [GlobalTheory.CompanionTheory.NullFr.Piece, GlobalTheory.CompanionTheory.NullFr.admitted, Set.mem_setOf_eq]
    rw [hco, hcm]
    refine ⟨⟨hez1, ?_, hP⟩, hz1, ?_, ?_, ?_, c₁, hc₁i, hc₁, ?_⟩
    · rw [← Matrix.smul_mul, ← Matrix.smul_mul, smul_sub, ← Matrix.smul_mul, hez2, hez1]
    · intro l k
      rw [GlobalTheory.CompanionTheory.NullFr.CoverStep.mul_gU_gD_apply]
      by_cases hk : k = i
      · rw [if_pos hk, hsum l, Matrix.sub_apply, hY₀i l]
        refine ⟨?_, ?_⟩
        · rw [mul_left_comm, key l, ← mul_assoc, Units.inv_mul, one_mul]
          exact (hy₁ l).2
        · rw [← mul_assoc, hu', key2 l]
          exact (hY l i).2
      · have hE : (GlobalTheory.CompanionTheory.NullFr.yc P z - GlobalTheory.CompanionTheory.NullFr.yU i y₀) l k =
            GlobalTheory.CompanionTheory.NullFr.yc P z l k := by
          simp [GlobalTheory.CompanionTheory.NullFr.yU, hk]
        rw [if_neg hk, hE]
        exact hY l k
    · intro p k hk
      rw [GlobalTheory.CompanionTheory.NullFr.CoverStep.mul_gU_gD_apply, if_neg hk]
      exact hKo p k hk
    · intro p
      rw [GlobalTheory.CompanionTheory.NullFr.CoverStep.mul_gU_gD_apply, if_pos rfl, ← mul_assoc, hu', mul_sub,
        Finset.mul_sum]
      simp_rw [← mul_assoc, h1fc₀, zero_mul, Finset.sum_const_zero, sub_zero]
      exact hKi p
    · intro p
      have hR : ∑ k, c₁ k * (GlobalTheory.CompanionTheory.NullFr.vc P z * GlobalTheory.CompanionTheory.NullFr.gU i (-c₀) *
          GlobalTheory.CompanionTheory.NullFr.gD i ((u⁻¹ : Aˣ) : A)) p k = ∑ k, c₁ k * GlobalTheory.CompanionTheory.NullFr.vc P z p k := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [GlobalTheory.CompanionTheory.NullFr.CoverStep.mul_gU_gD_apply]
        by_cases hk : k = i
        · simp [hk, hc₁i]
        · rw [if_neg hk]
      have hL : f * (GlobalTheory.CompanionTheory.NullFr.vc P z p i - ∑ k, c₀ k * GlobalTheory.CompanionTheory.NullFr.vc P z p k) =
          (u : A) * ∑ k, c₁ k * GlobalTheory.CompanionTheory.NullFr.vc P z p k := by
        rw [mul_sub, hfK p, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← mul_assoc, hfc₀, ← sub_mul, hc k, add_sub_cancel_left, mul_assoc]
      rw [hR, GlobalTheory.CompanionTheory.NullFr.CoverStep.mul_gU_gD_apply, if_pos rfl, mul_left_comm, hL,
        ← mul_assoc, Units.inv_mul, one_mul]
  · refine Prod.ext rfl ?_
    dsimp only
    rw [Matrix.mul_assoc _ (GlobalTheory.CompanionTheory.NullFr.gD i ((u⁻¹ : Aˣ) : A)) (GlobalTheory.CompanionTheory.NullFr.gD i (u : A)),
      hD, Matrix.mul_one, Matrix.mul_assoc _ (GlobalTheory.CompanionTheory.NullFr.gU i (-c₀)) (GlobalTheory.CompanionTheory.NullFr.gU i c₀), hS,
      Matrix.mul_one, sub_add_cancel]

end GlobalTheory.CompanionTheory.NullFr.CoverStep
