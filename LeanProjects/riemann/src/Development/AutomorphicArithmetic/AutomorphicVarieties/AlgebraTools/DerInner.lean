import Mathlib

open Polynomial Matrix IsLocalRing TensorProduct

theorem UpperTheory.V.AlgebraTools.der_inner :
    ∀ {K E : Type} [CommRing K] [Ring E] [Algebra K E] {σ : Type} [Fintype σ] [DecidableEq σ] (d : σ → Type) [∀ s, Fintype (d s)] [∀ s, DecidableEq (d s)] [∀ s, Nonempty (d s)] (j : (∀ s, Matrix (d s) (d s) K) →ₐ[K] E) (D : (∀ s, Matrix (d s) (d s) K) →ₗ[K] E), (∀ x y, D (x * y) = D x * j y + j x * D y) → ∃ Y : E, ∀ x, D x = Y * j x - j x * Y := by
  intro K E _ _ _ σ _ _ d _ _ _ j D hD
  let i0 : ∀ s, d s := fun s => Classical.arbitrary (d s)
  let u : ∀ s, d s → d s → (∀ s, Matrix (d s) (d s) K) :=
    fun s p q => Pi.single s (Matrix.single p q (1 : K))
  have hsame : ∀ s (p q r w : d s), u s p q * u s r w = if q = r then u s p w else 0 := by
    intro s p q r w
    simp only [u, ← Pi.single_mul]
    split_ifs with h
    · subst h
      rw [Matrix.single_mul_single_same, one_mul]
    · rw [Matrix.single_mul_single_of_ne _ _ _ _ h, Pi.single_zero]
  have hne : ∀ s t (p q : d s) (r w : d t), s ≠ t → u s p q * u t r w = 0 := by
    intro s t p q r w h
    funext x
    simp only [u, Pi.mul_apply, Pi.zero_apply]
    by_cases hx : x = s
    · subst hx
      rw [Pi.single_eq_of_ne h, mul_zero]
    · rw [Pi.single_eq_of_ne hx, zero_mul]
  have hone : ∑ s, ∑ k, u s k k = 1 := by
    funext x
    rw [Finset.sum_apply, Finset.sum_eq_single x]
    · rw [Finset.sum_apply]
      ext a b
      simp only [u, Pi.single_eq_same, Matrix.sum_apply, Matrix.single_apply, Pi.one_apply,
        Matrix.one_apply]
      by_cases hab : a = b
      · subst hab
        simp
      · rw [Finset.sum_eq_zero fun k _ => if_neg fun h => hab (h.1.symm.trans h.2)]
        simp [hab]
    · intro s _ hs
      rw [Finset.sum_apply]
      exact Finset.sum_eq_zero fun k _ => Pi.single_eq_of_ne (Ne.symm hs) _
    · intro h
      exact absurd (Finset.mem_univ _) h
  let a : E := ∑ s, ∑ k, j (u s k (i0 s)) * D (u s (i0 s) k)
  have key : ∀ t (p q : d t), D (u t p q) = j (u t p q) * a - a * j (u t p q) := by
    intro t p q
    have h1 : j (u t p q) * a = j (u t p (i0 t)) * D (u t (i0 t) q) := by
      simp only [a, Finset.mul_sum, ← mul_assoc, ← map_mul]
      rw [Finset.sum_eq_single t]
      · rw [Finset.sum_eq_single q]
        · rw [hsame, if_pos rfl]
        · intro k _ hk
          rw [hsame, if_neg (Ne.symm hk), map_zero, zero_mul]
        · intro h
          exact absurd (Finset.mem_univ _) h
      · intro s _ hs
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [hne t s _ _ _ _ (Ne.symm hs), map_zero, zero_mul]
      · intro h
        exact absurd (Finset.mem_univ _) h
    have hS1 : ∑ s, ∑ k, j (u s k (i0 s)) * D (u s (i0 s) k * u t p q)
        = j (u t p (i0 t)) * D (u t (i0 t) q) := by
      rw [Finset.sum_eq_single t]
      · rw [Finset.sum_eq_single p]
        · rw [hsame, if_pos rfl]
        · intro k _ hk
          rw [hsame, if_neg hk, map_zero, mul_zero]
        · intro h
          exact absurd (Finset.mem_univ _) h
      · intro s _ hs
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [hne s t _ _ _ _ hs, map_zero, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ _) h
    have hS2 : ∑ s, ∑ k, j (u s k (i0 s)) * j (u s (i0 s) k) = 1 := by
      simp only [← map_mul, hsame, eq_self_iff_true, if_true]
      simp only [← map_sum]
      rw [hone, map_one]
    have e : a * j (u t p q) = ∑ s, ∑ k, (j (u s k (i0 s)) * D (u s (i0 s) k * u t p q)
        - j (u s k (i0 s)) * j (u s (i0 s) k) * D (u t p q)) := by
      simp only [a, Finset.sum_mul]
      refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun k _ => ?_
      rw [hD]
      noncomm_ring
    rw [h1, e]
    simp only [Finset.sum_sub_distrib, ← Finset.sum_mul, hS1, hS2, one_mul]
    abel
  refine ⟨-a, fun x => ?_⟩
  have hlin : D = (LinearMap.mulRight K a).comp j.toLinearMap
      - (LinearMap.mulLeft K a).comp j.toLinearMap := by
    refine (Pi.basis fun s => Matrix.stdBasis K (d s) (d s)).ext fun ji => ?_
    obtain ⟨t, p, q⟩ := ji
    rw [Pi.basis_apply, Matrix.stdBasis_eq_single]
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.mulRight_apply,
      LinearMap.mulLeft_apply, AlgHom.toLinearMap_apply]
    exact key t p q
  have hx := LinearMap.congr_fun hlin x
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.mulRight_apply,
    LinearMap.mulLeft_apply, AlgHom.toLinearMap_apply] at hx
  rw [hx]
  noncomm_ring
