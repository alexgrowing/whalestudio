import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.OddInvolution

theorem exists_pos_pow_idem {M : Type} [Monoid M] [Finite M] (x : M) :
    ∃ m : ℕ, 0 < m ∧ IsIdempotentElem (x ^ m) := by
  have key : ∀ i d : ℕ, 0 < d → x ^ (i + d) = x ^ i → ∃ m : ℕ, 0 < m ∧ IsIdempotentElem (x ^ m) := by
    intro i d hd h
    have h1 : ∀ t k : ℕ, x ^ (i + k + t * d) = x ^ (i + k) := by
      intro t k
      induction t with
      | zero => simp
      | succ t ih =>
        have : i + k + (t + 1) * d = (i + d) + (k + t * d) := by ring
        rw [this, pow_add, h, ← pow_add, ← add_assoc, ih]
    have hle : i ≤ (i + 1) * d := by nlinarith
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
    refine ⟨(i + 1) * d, by positivity, ?_⟩
    unfold IsIdempotentElem
    rw [← pow_add]
    have := h1 (i + 1) k
    rw [← hk] at this
    exact this
  obtain ⟨i, j, hij, h⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => x ^ n)
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · exact key i (j - i) (by omega) (by rw [Nat.add_sub_cancel' hlt.le]; exact h.symm)
  · exact key j (i - j) (by omega) (by rw [Nat.add_sub_cancel' hlt.le]; exact h)

theorem pow_idem_field {F : Type} [Field F] {u : F} {m : ℕ} (hm : 0 < m)
    (he : IsIdempotentElem (u ^ m)) : (u = 0 → u ^ m = 0) ∧ (u ≠ 0 → u ^ m = 1) := by
  refine ⟨fun h => by rw [h, zero_pow hm.ne'], fun h => ?_⟩
  have h2 : u ^ m * u ^ m = u ^ m * 1 := by rw [mul_one]; exact he
  exact mul_left_cancel₀ (pow_ne_zero _ h) h2

theorem isUnit_of_forall_maximal {R : Type} [CommRing R] {s : R}
    (h : ∀ m : Ideal R, m.IsMaximal → Ideal.Quotient.mk m s ≠ 0) : IsUnit s := by
  by_contra hs
  obtain ⟨m, hm, hsm⟩ := exists_max_ideal_of_mem_nonunits (show s ∈ nonunits R from hs)
  exact h m hm (Ideal.Quotient.eq_zero_iff_mem.mpr hsm)

theorem exists_anticommuting {R : Type} [CommRing R] [Finite R] (h2 : IsUnit (2 : R))
    (a b c : R) (h : a * a + b * c = 1) :
    ∃ p q r : R, IsUnit (p * p + q * r) ∧ 2 * a * p + b * r + c * q = 0 := by
  obtain ⟨n1, hn1, he1⟩ := exists_pos_pow_idem (b * c)
  obtain ⟨n2, hn2, he2⟩ := exists_pos_pow_idem ((b + c) ^ 2 + 4 * a ^ 2)
  set e1 := (b * c) ^ n1 with he1d
  set e2 := ((b + c) ^ 2 + 4 * a ^ 2) ^ n2 with he2d
  refine ⟨(1 - e1) * e2 * (b + c) + (1 - e1) * (1 - e2) * (b - c),
    e1 * b + (1 - e1) * e2 * (-2 * a) + (1 - e1) * (1 - e2) * (2 * a),
    e1 * (-c) + (1 - e1) * e2 * (-2 * a) + (1 - e1) * (1 - e2) * (-2 * a), ?_, by ring⟩
  apply isUnit_of_forall_maximal
  intro m hm
  letI := Ideal.Quotient.field m
  have h2' : Ideal.Quotient.mk m (2 : R) ≠ 0 := (h2.map (Ideal.Quotient.mk m)).ne_zero
  have hh := congrArg (Ideal.Quotient.mk m) h
  have q1 : Ideal.Quotient.mk m e1 = (Ideal.Quotient.mk m (b * c)) ^ n1 := by rw [he1d, map_pow]
  have q2 : Ideal.Quotient.mk m e2 = (Ideal.Quotient.mk m ((b + c) ^ 2 + 4 * a ^ 2)) ^ n2 := by
    rw [he2d, map_pow]
  have k1 := pow_idem_field hn1 (q1 ▸ he1.map (Ideal.Quotient.mk m))
  have k2 := pow_idem_field hn2 (q2 ▸ he2.map (Ideal.Quotient.mk m))
  rw [← q1] at k1
  rw [← q2] at k2
  simp only [map_add, map_mul, map_sub, map_one, map_neg, map_pow, map_ofNat] at hh k1 k2 h2' ⊢
  generalize Ideal.Quotient.mk m e1 = E1 at k1 k2 ⊢
  generalize Ideal.Quotient.mk m e2 = E2 at k1 k2 ⊢
  generalize Ideal.Quotient.mk m a = A at hh k1 k2 ⊢
  generalize Ideal.Quotient.mk m b = B at hh k1 k2 ⊢
  generalize Ideal.Quotient.mk m c = C at hh k1 k2 ⊢
  have h8 : (2 : R ⧸ m) * 2 * 2 ≠ 0 := by simp [h2']
  by_cases hBC : B * C = 0
  · rw [k1.1 hBC]
    by_cases hU : (B + C) ^ 2 + 4 * A ^ 2 = 0
    · rw [k2.1 hU]
      intro hz
      apply h8
      linear_combination -hz + hU - 8 * hh + 4 * hBC
    · rw [k2.2 hU]
      intro hz
      apply hU
      linear_combination hz
  · rw [k1.2 hBC]
    intro hz
    apply hBC
    linear_combination -hz

theorem exists_swap {R : Type} [CommRing R] [Finite R] (X : Matrix (Fin 2) (Fin 2) R)
    (h2 : IsUnit (2 : R)) (hdet : X.det = -1) (htr : X.trace = 0) :
    ∃ (Y : Matrix (Fin 2) (Fin 2) R) (s : R), IsUnit s ∧ Y * Y = s • (1 : Matrix (Fin 2) (Fin 2) R) ∧
      X * Y = -(Y * X) := by
  rw [Matrix.det_fin_two] at hdet
  rw [Matrix.trace_fin_two] at htr
  have hd : X 1 1 = -X 0 0 := by linear_combination htr
  have h : X 0 0 * X 0 0 + X 0 1 * X 1 0 = 1 := by
    rw [hd] at hdet; linear_combination -hdet
  obtain ⟨p, q, r, hs, hanti⟩ := exists_anticommuting h2 (X 0 0) (X 0 1) (X 1 0) h
  refine ⟨!![p, q; r, -p], p * p + q * r, hs, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, hd, Matrix.vecMul, dotProduct] <;>
      first | linear_combination hanti | ring

theorem card_fixed_eq (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] [Finite R]
    (X : Matrix (Fin 2) (Fin 2) R) (h2 : IsUnit (2 : R)) (hXX : X * X = 1) (hdet : X.det = -1)
    (htr : X.trace = 0) : Nat.card {v : Fin 2 → R // X *ᵥ v = v} = Nat.card R := by
  obtain ⟨Y, s, hs, hYY, hXY⟩ := exists_swap X h2 hdet htr
  have hXXv : ∀ v : Fin 2 → R, X *ᵥ (X *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, hXX, Matrix.one_mulVec]
  have hYYv : ∀ v : Fin 2 → R, Y *ᵥ (Y *ᵥ v) = s • v := fun v => by
    rw [Matrix.mulVec_mulVec, hYY]
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.one_apply]
  have hXYv : ∀ v : Fin 2 → R, X *ᵥ (Y *ᵥ v) = -(Y *ᵥ (X *ᵥ v)) := fun v => by
    rw [Matrix.mulVec_mulVec, hXY, Matrix.neg_mulVec, Matrix.mulVec_mulVec]
  have hsu : ((hs.unit⁻¹ : Rˣ) : R) * s = 1 := by simp
  let e : {v : Fin 2 → R // X *ᵥ v = v} ≃ {v : Fin 2 → R // X *ᵥ v = -v} :=
    { toFun := fun v => ⟨Y *ᵥ v.1, by rw [hXYv, v.2]⟩
      invFun := fun w => ⟨((hs.unit⁻¹ : Rˣ) : R) • (Y *ᵥ w.1), by
        rw [Matrix.mulVec_smul, hXYv, w.2, Matrix.mulVec_neg, neg_neg]⟩
      left_inv := fun v => by
        apply Subtype.ext
        simp only [hYYv, smul_smul, hsu, one_smul]
      right_inv := fun w => by
        apply Subtype.ext
        simp only [Matrix.mulVec_smul, hYYv, smul_smul, hsu, one_smul] }
  have ht : ((h2.unit⁻¹ : Rˣ) : R) * 2 = 1 := by simp
  set t : R := ((h2.unit⁻¹ : Rˣ) : R)
  let f : (Fin 2 → R) ≃ {v : Fin 2 → R // X *ᵥ v = v} × {v : Fin 2 → R // X *ᵥ v = -v} :=
    { toFun := fun v => (⟨t • (v + X *ᵥ v), by
          rw [Matrix.mulVec_smul, Matrix.mulVec_add, hXXv, add_comm]⟩,
        ⟨t • (v - X *ᵥ v), by
          rw [Matrix.mulVec_smul, Matrix.mulVec_sub, hXXv, ← smul_neg, neg_sub]⟩)
      invFun := fun pq => pq.1.1 + pq.2.1
      left_inv := fun v => by
        funext i
        simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        linear_combination (v i) * ht
      right_inv := fun pq => by
        obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ := pq
        ext i
        · simp only [Matrix.mulVec_add, hp, hq, Pi.add_apply, Pi.smul_apply, Pi.neg_apply,
            smul_eq_mul]
          linear_combination (p i) * ht
        · simp only [Matrix.mulVec_add, hp, hq, Pi.add_apply, Pi.smul_apply, Pi.neg_apply,
            Pi.sub_apply, smul_eq_mul]
          linear_combination (q i) * ht }
  have h1 : Nat.card (Fin 2 → R) =
      Nat.card {v : Fin 2 → R // X *ᵥ v = v} * Nat.card {v : Fin 2 → R // X *ᵥ v = -v} := by
    rw [Nat.card_congr f, Nat.card_prod]
  have h3 : Nat.card (Fin 2 → R) = Nat.card R * Nat.card R := by
    rw [Nat.card_fun]; simp [sq]
  have hsq : Nat.card {v : Fin 2 → R // X *ᵥ v = v} * Nat.card {v : Fin 2 → R // X *ᵥ v = v} =
      Nat.card R * Nat.card R := by
    rw [← h3, h1, Nat.card_congr e]
  exact Nat.mul_self_inj.mp hsq

theorem card_fixed (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] [Finite R]
    (X : Matrix (Fin 2) (Fin 2) R) : IsUnit (2 : R) → X * X = 1 → X.det = -1 → X.trace = 0 →
      Nat.card {v : Fin 2 → R // X *ᵥ v = v} = Nat.card R :=
  fun h2 hXX hdet htr => card_fixed_eq l R X h2 hXX hdet htr

end GlobalTheory.OddInvolution
