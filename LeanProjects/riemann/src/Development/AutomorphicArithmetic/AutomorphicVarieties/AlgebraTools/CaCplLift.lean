import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IsCplAtSelf
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCplMap

open IsLocalRing UpperTheory.V.AlgebraTools

private theorem level_map {R : Type} [CommRing R] {p : Ideal R} {B : Type} [CommRing B]
    [IsLocalRing B] [Algebra R B] (h : IsCplAt R p B) (n : ℕ) {D : Type} [CommRing D]
    (g : R →+* D) (hu : ∀ s, s ∉ p → IsUnit (g s)) (hz : ∀ a, a ∈ p ^ n → g a = 0) :
    ∃ f : B →+* D, ∀ (b : B) (a s : R), s ∉ p →
      algebraMap R B s * b - algebraMap R B a ∈ maximalIdeal B ^ n → g s * f b = g a := by
  have hP := h.isPrime
  choose A S hS hAS using h.dense n
  have wd : ∀ (b : B) (a s a' s' : R), s ∉ p → s' ∉ p →
      algebraMap R B s * b - algebraMap R B a ∈ maximalIdeal B ^ n →
      algebraMap R B s' * b - algebraMap R B a' ∈ maximalIdeal B ^ n → g s * g a' = g s' * g a := by
    intro b a s a' s' _ hs' h1 h2
    have hm : algebraMap R B (s * a' - s' * a) ∈ maximalIdeal B ^ n := by
      have hid : algebraMap R B (s * a' - s' * a) = algebraMap R B s' *
          (algebraMap R B s * b - algebraMap R B a) - algebraMap R B s *
          (algebraMap R B s' * b - algebraMap R B a') := by
        simp only [map_sub, map_mul]
        ring
      rw [hid]
      exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)
    obtain ⟨t, ht, hta⟩ := h.strict n _ hm
    have h0 := hz _ hta
    rw [map_mul, (hu t ht).mul_right_eq_zero, map_sub, map_mul, map_mul, sub_eq_zero] at h0
    exact h0
  let F : B → D := fun b => ↑(hu _ (hS b)).unit⁻¹ * g (A b)
  have hF0 : ∀ b, g (S b) * F b = g (A b) := by
    intro b
    simp only [F, ← mul_assoc, IsUnit.mul_val_inv, one_mul]
  have spec : ∀ (b : B) (a s : R), s ∉ p →
      algebraMap R B s * b - algebraMap R B a ∈ maximalIdeal B ^ n → g s * F b = g a := by
    intro b a s hs hb
    apply (hu _ (hS b)).mul_left_cancel
    rw [← mul_assoc, mul_comm (g (S b)), mul_assoc, hF0, wd b (A b) (S b) a s (hS b) hs (hAS b) hb]
  have eq_of : ∀ (b : B) (y : D) (a s : R), s ∉ p →
      algebraMap R B s * b - algebraMap R B a ∈ maximalIdeal B ^ n → g a = g s * y → F b = y := by
    intro b y a s hs hb hy
    exact (hu s hs).mul_left_cancel ((spec b a s hs hb).trans hy)
  have hprod : ∀ x y : B, S x * S y ∉ p := fun x y hm => (hP.mem_or_mem hm).elim (hS x) (hS y)
  refine ⟨{ toFun := F, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, spec⟩
  · refine eq_of 1 1 1 1 ?_ ?_ (by simp)
    · intro h1
      exact hP.ne_top ((Ideal.eq_top_iff_one _).2 h1)
    · simp
  · intro x y
    refine eq_of (x * y) _ (A x * A y) (S x * S y) (hprod x y) ?_ ?_
    · have hid : algebraMap R B (S x * S y) * (x * y) - algebraMap R B (A x * A y) =
          algebraMap R B (S x) * x * (algebraMap R B (S y) * y - algebraMap R B (A y)) +
          algebraMap R B (A y) * (algebraMap R B (S x) * x - algebraMap R B (A x)) := by
        simp only [map_mul]
        ring
      rw [hid]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (hAS y)) (Ideal.mul_mem_left _ _ (hAS x))
    · show g (A x * A y) = g (S x * S y) * (F x * F y)
      rw [map_mul, map_mul, ← hF0 x, ← hF0 y]
      ring
  · refine eq_of 0 0 0 1 ?_ ?_ (by simp)
    · intro h1
      exact hP.ne_top ((Ideal.eq_top_iff_one _).2 h1)
    · simp
  · intro x y
    refine eq_of (x + y) _ (S y * A x + S x * A y) (S x * S y) (hprod x y) ?_ ?_
    · have hid : algebraMap R B (S x * S y) * (x + y) - algebraMap R B (S y * A x + S x * A y) =
          algebraMap R B (S y) * (algebraMap R B (S x) * x - algebraMap R B (A x)) +
          algebraMap R B (S x) * (algebraMap R B (S y) * y - algebraMap R B (A y)) := by
        simp only [map_mul, map_add]
        ring
      rw [hid]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (hAS x)) (Ideal.mul_mem_left _ _ (hAS y))
    · show g (S y * A x + S x * A y) = g (S x * S y) * (F x + F y)
      rw [map_add, map_mul, map_mul, map_mul, ← hF0 x, ← hF0 y]
      ring

theorem UpperTheory.V.AlgebraTools.IsCplAt.existsUnique_lift :
    ∀ (R : Type) [CommRing R] (p : Ideal R) (B : Type) [CommRing B] [IsLocalRing B] [Algebra R B], IsCplAt R p B →
      ∀ (C : Type) [CommRing C] [IsLocalRing C] [IsAdicComplete (maximalIdeal C) C] (φ : R →+* C),
      (maximalIdeal C).comap φ = p → ∃! ψ : B →+* C, ψ.comp (algebraMap R B) = φ := by
  intro R _ p B _ _ _ hB C _ _ _ φ hφ
  have hpI : ∀ n, ∀ a ∈ p ^ n, φ a ∈ maximalIdeal C ^ n := by
    intro n a ha
    have hle : Ideal.map φ p ≤ maximalIdeal C := by
      rw [← hφ]
      exact Ideal.map_comap_le
    have hmap : Ideal.map φ (p ^ n) ≤ maximalIdeal C ^ n := by
      rw [Ideal.map_pow]
      exact Ideal.pow_right_mono hle n
    exact hmap (Ideal.mem_map_of_mem φ ha)
  have hunit : ∀ s, s ∉ p → IsUnit (φ s) := by
    intro s hs
    by_contra hn
    apply hs
    rw [← hφ, Ideal.mem_comap]
    exact (IsLocalRing.mem_maximalIdeal _).2 hn
  let g : ∀ n, R →+* C ⧸ maximalIdeal C ^ n := fun n => (Ideal.Quotient.mk (maximalIdeal C ^ n)).comp φ
  have hu : ∀ n s, s ∉ p → IsUnit (g n s) := fun n s hs =>
    (hunit s hs).map (Ideal.Quotient.mk (maximalIdeal C ^ n))
  have hz : ∀ n a, a ∈ p ^ n → g n a = 0 := fun n a ha => Ideal.Quotient.eq_zero_iff_mem.2 (hpI n a ha)
  choose f hf using fun n => level_map hB n (g n) (hu n) (hz n)
  have lvl : ∀ n (k : B → C ⧸ maximalIdeal C ^ n), (∀ (b : B) (a s : R), s ∉ p →
      algebraMap R B s * b - algebraMap R B a ∈ maximalIdeal B ^ n → g n s * k b = g n a) →
      ∀ b, k b = f n b := by
    intro n k hk b
    obtain ⟨a, s, hs, hb⟩ := hB.dense n b
    exact (hu n s hs).mul_left_cancel ((hk b a s hs hb).trans (hf n b a s hs hb).symm)
  have compat : ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorPow (maximalIdeal C) hle).comp (f n) = f m := by
    intro m n hle
    ext b
    obtain ⟨a, s, hs, hb⟩ := hB.dense n b
    have hbm : algebraMap R B s * b - algebraMap R B a ∈ maximalIdeal B ^ m :=
      Ideal.pow_le_pow_right hle hb
    apply (hu m s hs).mul_left_cancel
    show g m s * Ideal.Quotient.factorPow (maximalIdeal C) hle (f n b) = g m s * f m b
    rw [hf m b a s hs hbm]
    have hc := congrArg (Ideal.Quotient.factorPow (maximalIdeal C) hle) (hf n b a s hs hb)
    rw [map_mul] at hc
    have hg : ∀ x, Ideal.Quotient.factorPow (maximalIdeal C) hle (g n x) = g m x := by
      intro x
      simp [g]
    rw [hg, hg] at hc
    exact hc
  have h1p : (1 : R) ∉ p := fun h1 => hB.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  have hmk : ∀ n b, Ideal.Quotient.mk (maximalIdeal C ^ n)
      (IsAdicComplete.liftRingHom (maximalIdeal C) f compat b) = f n b :=
    fun n b => IsAdicComplete.mk_liftRingHom (maximalIdeal C) f compat n b
  refine ⟨IsAdicComplete.liftRingHom (maximalIdeal C) f compat, ?_, ?_⟩
  · apply DFunLike.coe_injective
    apply IsHausdorff.funext' (maximalIdeal C)
    intro n r
    rw [RingHom.comp_apply, hmk]
    apply (hu n 1 h1p).mul_left_cancel
    rw [hf n (algebraMap R B r) r 1 h1p (by simp), map_one, one_mul]
    rfl
  · intro ψ' hψ'
    apply IsAdicComplete.eq_liftRingHom (maximalIdeal C) f compat ψ'
    intro n
    ext b
    rw [RingHom.comp_apply]
    refine lvl n (fun b => Ideal.Quotient.mk (maximalIdeal C ^ n) (ψ' b)) ?_ b
    intro b a s hs hb
    have hmap : Ideal.map ψ' (maximalIdeal B ^ n) ≤ maximalIdeal C ^ n := by
      rw [← IsCplAt.map_pow_eq R p B hB n, Ideal.map_map, hψ', Ideal.map_le_iff_le_comap]
      intro c hc
      exact hpI n c hc
    have h0 := Ideal.Quotient.eq_zero_iff_mem.2 (hmap (Ideal.mem_map_of_mem _ hb))
    have e : ∀ x, ψ' (algebraMap R B x) = φ x := fun x => by rw [← RingHom.comp_apply, hψ']
    rw [map_sub, map_mul, e, e, map_sub, map_mul, sub_eq_zero] at h0
    exact h0
