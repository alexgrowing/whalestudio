import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
open MvPolynomial GlobalTheory.ArInt

namespace GlobalTheory.PolarFlat

theorem altSum_eq_zero {M : Type} [AddCommGroup M] (D : ℕ) (j : Fin D) (g : Finset (Fin D) → M)
    (hg : ∀ S, j ∉ S → g (insert j S) = g S) :
    ∑ S : Finset (Fin D), ((-1 : ℤ) ^ S.card) • g S = 0 := by
  rw [← Finset.powerset_univ, ← Finset.insert_erase (Finset.mem_univ j),
    Finset.sum_powerset_insert (Finset.notMem_erase j _), ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun S hS => ?_
  have hjS : j ∉ S := fun h => Finset.notMem_erase j _ (Finset.mem_powerset.1 hS h)
  rw [Finset.card_insert_of_notMem hjS, hg S hjS, pow_succ]
  simp

theorem signCount (D : ℕ) (f : Fin D → Fin D) :
    ∑ S : Finset (Fin D), ((-1 : ℤ) ^ S.card) • (if ∀ t, f t ∈ S then (1 : ℤ) else 0) =
      if Function.Surjective f then (-1) ^ D else 0 := by
  split_ifs with hf
  · rw [Finset.sum_eq_single Finset.univ]
    · simp
    · intro S _ hS
      have : ¬ ∀ t, f t ∈ S := by
        intro hall
        apply hS
        ext k
        obtain ⟨t, rfl⟩ := hf k
        simp [hall t]
      simp [this]
    · intro h; exact absurd (Finset.mem_univ _) h
  · simp only [Function.Surjective, not_forall] at hf
    obtain ⟨k, hk⟩ := hf
    refine altSum_eq_zero D k _ fun S _ => ?_
    have : (∀ t, f t ∈ insert k S) ↔ ∀ t, f t ∈ S := by
      refine forall_congr' fun t => ?_
      rw [Finset.mem_insert]
      exact ⟨fun h => h.resolve_left fun e => hk ⟨t, e⟩, Or.inr⟩
    simp only [this]

theorem pow_sum_ite (D : ℕ) (S : Finset (Fin D)) :
    (∑ i, if i ∈ S then (X i : MvPolynomial (Fin D) ℝ) else 0) ^ D =
      ∑ f : Fin D → Fin D, if ∀ t, f t ∈ S then ∏ t, (X (f t) : MvPolynomial (Fin D) ℝ) else 0 := by
  rw [← Fin.prod_const, Fintype.prod_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Finset.prod_ite_zero]
  simp

theorem polar (D : ℕ) :
    ∑ S : Finset (Fin D), ((-1 : ℤ) ^ S.card) • (∑ i, if i ∈ S then (X i : MvPolynomial (Fin D) ℝ) else 0) ^ D =
      (Finset.univ.filter fun f : Fin D → Fin D => Function.Surjective f).card •
        (((-1 : ℤ) ^ D) • ∏ k, (X k : MvPolynomial (Fin D) ℝ)) := by
  simp_rw [pow_sum_ite, Finset.smul_sum]
  rw [Finset.sum_comm]
  have step : ∀ f : Fin D → Fin D, ∑ S : Finset (Fin D),
      ((-1 : ℤ) ^ S.card) • (if ∀ t, f t ∈ S then ∏ t, (X (f t) : MvPolynomial (Fin D) ℝ) else 0) =
      (if Function.Surjective f then ((-1 : ℤ) ^ D) • ∏ k, (X k : MvPolynomial (Fin D) ℝ) else 0) := by
    intro f
    have e1 : ∀ S : Finset (Fin D), ((-1 : ℤ) ^ S.card) •
        (if ∀ t, f t ∈ S then ∏ t, (X (f t) : MvPolynomial (Fin D) ℝ) else 0) =
        (((-1 : ℤ) ^ S.card) • (if ∀ t, f t ∈ S then (1 : ℤ) else 0)) • ∏ t, (X (f t) : MvPolynomial (Fin D) ℝ) := by
      intro S; split_ifs <;> simp
    simp_rw [e1]
    rw [← Finset.sum_smul, signCount]
    split_ifs with hf
    · congr 1
      exact Equiv.prod_comp (Equiv.ofBijective f ⟨Finite.injective_iff_surjective.2 hf, hf⟩)
        (fun k => (X k : MvPolynomial (Fin D) ℝ))
    · simp
  simp_rw [step]
  rw [← Finset.sum_filter, Finset.sum_const]

end GlobalTheory.PolarFlat

theorem GlobalTheory.Div.polar_prod_eq_zero (D : ℕ) (Ψ : MvPolynomial (Fin D) ℝ →ₗ[ℝ] ℝ) (j : Fin D)
    (h : ∀ n : Fin D → ℤ, Ψ (lin (fun i => (n i : ℝ)) ^ D) =
      Ψ (lin (fun i => (Function.update n j 0 i : ℝ)) ^ D)) :
    Ψ (∏ k, MvPolynomial.X k) = 0 := by
  classical
  let e : Finset (Fin D) → Fin D → ℤ := fun S i => if i ∈ S then 1 else 0
  have hlin : ∀ S, lin (fun i => ((e S i : ℤ) : ℝ)) = ∑ i, if i ∈ S then (X i : MvPolynomial (Fin D) ℝ) else 0 := by
    intro S
    unfold lin
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : i ∈ S <;> simp [e, hi]
  have hB : ∑ S : Finset (Fin D), ((-1 : ℤ) ^ S.card) •
      Ψ ((∑ i, if i ∈ S then (X i : MvPolynomial (Fin D) ℝ) else 0) ^ D) = 0 := by
    refine GlobalTheory.PolarFlat.altSum_eq_zero D j _ fun S hj => ?_
    have hu : Function.update (e (insert j S)) j 0 = e S := by
      funext i
      by_cases hi : i = j
      · subst hi; simp [e, hj]
      · simp [e, hi, Function.update_of_ne hi]
    rw [← hlin (insert j S), ← hlin S, h, hu]
  have hP := congrArg Ψ (GlobalTheory.PolarFlat.polar D)
  rw [map_sum] at hP
  simp_rw [map_zsmul] at hP
  rw [hB, map_nsmul, map_zsmul] at hP
  have hcard : (Finset.univ.filter fun f : Fin D → Fin D => Function.Surjective f).card ≠ 0 := by
    apply Finset.card_ne_zero_of_mem (a := id)
    simp [Function.surjective_id]
  have h1 := (smul_eq_zero.1 hP.symm).resolve_left hcard
  rw [zsmul_eq_mul] at h1
  exact (mul_eq_zero.1 h1).resolve_left (by simp)
