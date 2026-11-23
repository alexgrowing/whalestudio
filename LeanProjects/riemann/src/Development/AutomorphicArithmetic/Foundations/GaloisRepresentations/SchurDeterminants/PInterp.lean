import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.SchurYOffClr
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PairSplit

noncomputable section

open Finset MvPolynomial

namespace UpperTheory.Gal.Schur

theorem interp_of : SpanProd → Expand → Extract → DenseCoset → Interp := by
  intro hS hE hX hC O K ι _ _ _ _ τ hτ n P hP
  classical
  obtain ⟨k₀, hk₀⟩ := hS K ι n P hP
  refine ⟨k₀, fun k hk N hN a Q hQ => ?_⟩
  obtain ⟨w, hw⟩ := hk₀ k hk
  let A := {α : Fin k → O // (∀ s, N ∣ α s - a s) ∧ eval (pt τ α) Q ≠ 0}
  let x : A → ι × Fin k → K := fun α => pt τ α.1
  have hdense : ZDense (Set.range x) := by
    have hset : Set.range x =
        {z | ∃ α, (∀ s, N ∣ α s - a s) ∧ eval (pt τ α) Q ≠ 0 ∧ z = pt τ α} := by
      ext z
      constructor
      · rintro ⟨α, rfl⟩
        exact ⟨α.1, α.2.1, α.2.2, rfl⟩
      · rintro ⟨α, h1, h2, rfl⟩
        exact ⟨⟨α, h1, h2⟩, rfl⟩
    rw [hset]
    exact hC O K ι τ hτ N hN k a Q hQ
  have he : Function.Injective
      (fun (m : ι × Fin k → Fin (n + 1)) (p : ι × Fin k) => (m p : ℕ)) := by
    intro m₁ m₂ h
    funext p
    exact Fin.ext (congrFun h p)
  obtain ⟨c, hc⟩ := hX K (ι × Fin k) A (ι × Fin k → Fin (n + 1)) x hdense _ he w
  refine ⟨c.mapDomain Subtype.val, ?_, ?_⟩
  · intro α hα
    obtain ⟨β, -, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hα)
    exact β.2
  · intro R _ _ g
    let F : (Fin k → O) → R := fun α => ∏ t, ∏ s, detOne (algebraMap K R (τ t (α s))) (g t)
    have hmd : ((c.mapDomain Subtype.val).sum fun α (r : K) => r • F α) =
        c.sum fun β (r : K) => r • F β.1 := by
      apply Finsupp.sum_mapDomain_index
      · intro _
        exact zero_smul K _
      · intro _ r₁ r₂
        exact add_smul r₁ r₂ _
    change ((c.mapDomain Subtype.val).sum fun α (r : K) => r • F α) = _
    rw [hmd]
    have hexp : ∀ β : A, F β.1 =
        ∑ m : ι × Fin k → Fin (n + 1), algebraMap K R (∏ p, x β p ^ (m p : ℕ)) *
          ∏ p : ι × Fin k, (-1) ^ (m p : ℕ) * aeval (g p.1) (esymm (Fin n) K (m p : ℕ)) := by
      intro β
      have h := hE K R (ι × Fin k) n (fun p => algebraMap K R (pt τ β.1 p)) (fun p => g p.1)
      rw [Fintype.prod_prod_type] at h
      simp only [pt] at h
      simp only [F]
      rw [h]
      apply Finset.sum_congr rfl
      intro m _
      simp only [x, pt, map_prod, map_pow]
    simp only [Finsupp.sum, hexp]
    rw [hw R g]
    simp_rw [Finset.smul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro m _
    rw [← hc m, Finsupp.sum, Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro β _
    rw [Algebra.smul_def, Algebra.smul_def, map_mul]
    ring

end UpperTheory.Gal.Schur
