import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkEquivInl
open NumberField MeasureTheory GlobalTheory.CuspRep

noncomputable section

namespace GlobalTheory.LeviGA

open Matrix

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a r : ℕ}

theorem mul_mul_upper {R : Type} [CommRing R] (A N B : Matrix (Fin a) (Fin a) R)
    (hA : ∀ k p : Fin a, ((k : ℕ) < r ↔ (p : ℕ) < r) ∨ A k p = 0)
    (hB : ∀ q l : Fin a, ((q : ℕ) < r ↔ (l : ℕ) < r) ∨ B q l = 0)
    (hN : ∀ p q : Fin a, ¬((p : ℕ) < r ∧ r ≤ (q : ℕ)) → N p q = 0)
    (k l : Fin a) (hkl : ¬((k : ℕ) < r ∧ r ≤ (l : ℕ))) : (A * N * B) k l = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun q _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_eq_zero fun p _ => ?_
  by_cases hpq : (p : ℕ) < r ∧ r ≤ (q : ℕ)
  · rcases hA k p with h1 | h1
    · rcases hB q l with h2 | h2
      · exact absurd ⟨h1.2 hpq.1, by by_contra h; exact absurd (h2.2 (by omega)) (by omega)⟩ hkl
      · rw [h2, mul_zero]
    · rw [h1, zero_mul, zero_mul]
  · rw [hN p q hpq, mul_zero, zero_mul]

theorem lieD_single_blkGL (hr : r ≤ a) (f : Sm E a)
    (hf : ∀ (x : BlockIx a r → Ad E) (g : GA E a), f.1 (unip x * g) = f.1 g)
    (i j : Fin a) (hi : (i : ℕ) < r) (hj : r ≤ (j : ℕ)) (p : GA E r × GA E (a - r)) (x : Cinf E) :
    lieD (toL (Matrix.single i j x)) f.1 (blkGL hr p) = 0 := by
  set m : GA E a := blkGL hr p with hm
  set S : Matrix (Fin a) (Fin a) (Cinf E) := Matrix.single i j x with hS
  have hij : j ≠ i := fun h => by rw [h] at hj; omega
  have hSS : S * S = 0 := by rw [hS]; simp [hij, hij.symm]
  let c : ℝ → GL (Fin a) (Cinf E) := fun t =>
    ⟨1 + t • S, 1 - t • S, by simp [mul_sub, add_mul, smul_mul_smul_comm, hSS],
      by simp [sub_mul, mul_add, smul_mul_smul_comm, hSS]⟩
  have h0 : c 0 = 1 := Units.ext (by simp [c])
  have hc : HasDerivAt (fun t => toL (c t).val) (toL S) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const (toL S)).const_add (toL (1 : Matrix (Fin a) (Fin a) (Cinf E)))
    rw [one_smul] at this
    exact this
  have hd := hasDerivAt_curve f m c (toL S) h0 hc

  have hconst : ∀ t, f.1 (m * infGL E a (c t)) = f.1 m := by
    intro t
    set N : Matrix (Fin a) (Fin a) (Ad E) := matN a (sInf E) (t • S) with hN
    have hinf : (infGL E a (c t)).val = 1 + N := by
      change 1 - matN a (sInf E) 1 + matN a (sInf E) (1 + t • S) = 1 + N
      rw [map_add]; abel
    have hNsupp : ∀ p q : Fin a, ¬((p : ℕ) < r ∧ r ≤ (q : ℕ)) → N p q = 0 := by
      intro p q hpq
      have : (t • S) p q = 0 := by
        rw [hS, Matrix.smul_apply]
        by_cases e : p = i ∧ q = j
        · exact absurd (by rw [e.1, e.2]; exact ⟨hi, hj⟩) hpq
        · rw [Matrix.single_apply_of_ne (h := by tauto), smul_zero]
      change sInf E ((t • S) p q) = 0
      rw [this, map_zero]
    have hinv : m⁻¹ = blkGL hr p⁻¹ := by rw [hm, map_inv]
    let y : BlockIx a r → Ad E := fun q => (m.val * N * (m⁻¹).val) q.1.1 q.1.2
    have hy : nilM y = m.val * N * (m⁻¹).val := by
      ext k l
      simp only [nilM, Matrix.of_apply, y]
      split_ifs with h
      · rfl
      · exact (mul_mul_upper _ _ _ (blkGL_block hr p) (by rw [hinv]; exact blkGL_block hr _) hNsupp k l h).symm
    have e : m * infGL E a (c t) = unip y * m := by
      apply Units.ext
      change m.val * (infGL E a (c t)).val = (1 + nilM y) * m.val
      rw [hinf, hy, add_mul, one_mul, mul_add, mul_one, mul_assoc _ _ m.val,
        Units.inv_mul, mul_one]
    rw [e, hf]
  have hfun : (fun t => f.1 (m * infGL E a (c t))) = fun _ => f.1 m := funext hconst
  rw [hfun] at hd
  exact hd.unique (hasDerivAt_const 0 _)

theorem Eop_upper_blkGL_eq_zero :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a r : ℕ) (hr : r ≤ a) (f : Sm E a),
      (∀ (x : BlockIx a r → Ad E) (g : GA E a), f.1 (unip x * g) = f.1 g) → ∀ (τ : E →+* ℂ) (i j : Fin a),
        (i : ℕ) < r → r ≤ (j : ℕ) → ∀ (m₁ : GA E r) (m₂ : GA E (a - r)),
          (Eop τ i j f).1 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂)) = 0 := by
  intro E _ _ _ a r hr f hf τ i j hi hj m₁ m₂
  have key : ∀ x : Cinf E, (lieS E a i j x f).1 (blkGL hr (m₁, m₂)) = 0 := fun x =>
    lieD_single_blkGL hr f hf i j hi hj (m₁, m₂) x
  simp only [Eop, LinearMap.smul_apply, LinearMap.sub_apply, Submodule.coe_smul, Submodule.coe_sub, Pi.smul_apply,
    Pi.sub_apply, key, smul_zero, sub_zero]

end GlobalTheory.LeviGA
