import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.OrdReadOf

open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.splitAlg_of :
    SplitAlg := by
  classical
  intro κ B Λ _ _ _ _ _ _ _ hcard ε g
  have hli := linearIndependent_toLinearMap κ B κ
  haveI : Finite (B →ₐ[κ] κ) := hli.finite
  letI := Fintype.ofFinite (B →ₐ[κ] κ)
  have hspan : Submodule.span κ (Set.range (AlgHom.toLinearMap : (B →ₐ[κ] κ) → B →ₗ[κ] κ)) = ⊤ := by
    apply hli.span_eq_top_of_card_eq_finrank'
    rw [← Nat.card_eq_fintype_card, hcard]
    exact (Subspace.dual_finrank_eq).symm
  have h0 : ∀ x : B, (∀ φ : B →ₐ[κ] κ, φ x = 0) → x = 0 := by
    intro x hx
    rw [← Module.forall_dual_apply_eq_zero_iff κ x]
    intro f
    have hf : f ∈ Submodule.span κ (Set.range (AlgHom.toLinearMap : (B →ₐ[κ] κ) → B →ₗ[κ] κ)) := by
      rw [hspan]; exact Submodule.mem_top
    induction hf using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨φ, rfl⟩ := hy
      exact hx φ
    | zero => rfl
    | add y z _ _ hy hz => simp [hy, hz]
    | smul a y _ hy => simp [hy]
  have hunit : ∀ y : Λ, ε y ≠ 0 → IsUnit y := by
    intro y hy
    by_contra h
    have hym : y ∈ IsLocalRing.maximalIdeal Λ := h
    have hk : RingHom.ker ε.toRingHom ≤ IsLocalRing.maximalIdeal Λ :=
      IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _)
    have hd : y - algebraMap κ Λ (ε y) ∈ RingHom.ker ε.toRingHom := by
      rw [RingHom.mem_ker]
      simp
    have hm : algebraMap κ Λ (ε y) ∈ IsLocalRing.maximalIdeal Λ := by
      have := Ideal.sub_mem _ hym (hk hd)
      simpa using this
    exact hm ((isUnit_iff_ne_zero.mpr hy).map (algebraMap κ Λ))
  ext b
  simp only [AlgHom.comp_apply, Algebra.ofId_apply]
  set S : Finset κ := Finset.univ.image (fun φ : B →ₐ[κ] κ => φ b) with hS
  set c := ε (g b) with hc
  have hqb : Polynomial.aeval b (∏ s ∈ S, (Polynomial.X - Polynomial.C s)) = 0 := by
    apply h0
    intro φ
    rw [← Polynomial.aeval_algHom_apply, Polynomial.coe_aeval_eq_eval, Polynomial.eval_prod]
    apply Finset.prod_eq_zero (i := φ b) (by simp [hS])
    simp
  have hq : Polynomial.aeval (g b) (∏ s ∈ S, (Polynomial.X - Polynomial.C s)) = 0 := by
    rw [Polynomial.aeval_algHom_apply, hqb, map_zero]
  have hcS : c ∈ S := by
    have h1 := congrArg ε hq
    rw [← Polynomial.aeval_algHom_apply, map_zero, Polynomial.coe_aeval_eq_eval,
      Polynomial.eval_prod, Finset.prod_eq_zero_iff] at h1
    obtain ⟨s, hs, hs0⟩ := h1
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hs0
    rw [hc, hs0]
    exact hs
  rw [← Finset.mul_prod_erase S _ hcS, map_mul] at hq
  have hr : IsUnit (Polynomial.aeval (g b) (∏ s ∈ S.erase c, (Polynomial.X - Polynomial.C s))) := by
    apply hunit
    rw [← Polynomial.aeval_algHom_apply, Polynomial.coe_aeval_eq_eval, Polynomial.eval_prod,
      Finset.prod_ne_zero_iff]
    intro s hs
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    exact sub_ne_zero.mpr (Finset.ne_of_mem_erase hs).symm
  have h2 := hr.mul_left_eq_zero.mp hq
  simp only [map_sub, Polynomial.aeval_X, Polynomial.aeval_C] at h2
  exact sub_eq_zero.mp h2
