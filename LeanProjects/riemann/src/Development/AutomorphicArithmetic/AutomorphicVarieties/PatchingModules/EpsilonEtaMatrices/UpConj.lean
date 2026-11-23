import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.EpsilonEtaTensorDual
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.MemW1IffPattern

open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem up_mul {R : Type} [CommRing R] {n : ℕ} {P Q : Matrix (Fin n) (Fin n) R}
    (hP : ∀ i j, j < i → P i j = 0) (hQ : ∀ i j, j < i → Q i j = 0) :
    (∀ i j, j < i → (P * Q) i j = 0) ∧ ∀ i, (P * Q) i i = P i i * Q i i := by
  refine ⟨fun i j h => ?_, fun i => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases hc : c < i
    · rw [hP i c hc, zero_mul]
    · rw [hQ c j (lt_of_lt_of_le h (not_lt.1 hc)), mul_zero]
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_single i (fun c _ hc => ?_) (fun h => absurd (Finset.mem_univ i) h)
    rcases lt_or_gt_of_ne hc with h | h
    · rw [hP i c h, zero_mul]
    · rw [hQ c i h, mul_zero]

private theorem up_conj {R : Type} [CommRing R] {n : ℕ} {w wi r s y : Matrix (Fin n) (Fin n) R}
    (h1 : wi * w = 1) (h2 : w * wi = 1) (h3 : r * s = 1)
    (hr : ∀ i j, j < i → (wi * r * w) i j = 0) (hs : ∀ i j, j < i → (wi * s * w) i j = 0)
    (hy : ∀ i j, j < i → (wi * y * w) i j = 0) :
    (∀ i j, j < i → (wi * (r * y * s - y) * w) i j = 0) ∧ ∀ i, (wi * (r * y * s - y) * w) i i = 0 := by
  have key : wi * (r * y * s - y) * w = (wi * r * w) * (wi * y * w) * (wi * s * w) - wi * y * w := by
    rw [Matrix.mul_sub, Matrix.sub_mul]
    congr 1
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc w wi, h2, Matrix.one_mul, ← Matrix.mul_assoc w wi, h2, Matrix.one_mul]
  have hRS : (wi * r * w) * (wi * s * w) = 1 := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc w wi, h2, Matrix.one_mul, ← Matrix.mul_assoc r s, h3, Matrix.one_mul, h1]
  obtain ⟨hA, hAd⟩ := up_mul hr hy
  obtain ⟨hB, hBd⟩ := up_mul hA hs
  have hRSd := (up_mul hr hs).2
  rw [key]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [Matrix.sub_apply, hB i j hij, hy i j hij, sub_zero]
  · rw [Matrix.sub_apply, hBd i, hAd i]
    have hi := hRSd i
    rw [hRS, Matrix.one_apply_eq] at hi
    linear_combination (-(wi * y * w) i i) * hi

theorem UpperTheory.V.Pa.bMem :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (n : ℕ) (x : NP F n) (k : Kap x) (m : ℕ) (v : F.Vl) (y : k.M1 (x.Am m)) (β : F.Gv v → k.M1 (x.Am m)), y ∈ k.b1 (x.Am m) v → IsLocallyConstant β → (∀ g, (β g : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g)) = k.ρ1 (x.Am m) (F.φ v g) * y * k.ρ1 (x.Am m) (F.φ v g)⁻¹ - y) → β ∈ k.Zb (x.Am m) v := by
  intro l _ F n x k m v y β hy hβc hβ
  obtain ⟨hone, hmul, -, hw, -⟩ := rho1 l F n x k (x.Am m)
  obtain ⟨h1, h2⟩ := hw v
  have hT := (tri l F n x k (x.Am m) v).1
  have hinv : ∀ g : F.Gv v, k.ρ1 (x.Am m) (F.φ v g) * k.ρ1 (x.Am m) (F.φ v g)⁻¹ = 1 := by
    intro g
    rw [← hmul, mul_inv_cancel, hone]
  have hU : ∀ g : F.Gv v,
      (∀ i j, j < i → (k.wi1 (x.Am m) v * (β g : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g)) * k.w1 (x.Am m) v) i j = 0) ∧
      ∀ i, (k.wi1 (x.Am m) v * (β g : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g)) * k.w1 (x.Am m) v) i i = 0 := by
    intro g
    rw [hβ g]
    refine up_conj h1 h2 (hinv g) (hT g).1 ?_ (fun i j hij => hy i j hij)
    have hg := (hT g⁻¹).1
    rwa [map_inv] at hg
  refine ⟨hβc, fun g h => ?_, fun g => fun i j hij => (hU g).1 i j hij, fun g _ i => (hU g).2 i⟩
  rw [hβ (g * h), hβ g, hβ h, map_mul, hmul, _root_.mul_inv_rev, hmul]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  abel
