import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeModelVacuumTranslateClassesIndependent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Gam0
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmithNormalFormIntegralMatrix
open Matrix

noncomputable section

namespace GlobalTheory.Hk3.SnfGen

open GlobalTheory.Hk3.Smith

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem mulVec_int {a b : ℕ} {A : Matrix (Fin a) (Fin b) L} {x : Fin b → L}
    (hA : ∀ i j, A i j ∈ Formalism.UG.intL L) (hx : ∀ j, x j ∈ Formalism.UG.intL L) :
    ∀ i, (A *ᵥ x) i ∈ Formalism.UG.intL L := fun i => by
  simp only [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hA i k) (hx k)

theorem exp_of_gt {ϖ : L}
    (hϖ : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    {d : L} (hd : 1 < Valued.v d) :
    1 ≤ (-Formalism.UG.ordL d).toNat ∧ Valued.v (d * ϖ ^ (-Formalism.UG.ordL d).toNat) = 1 := by
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hϖ; exact WithZero.zero_ne_coe hϖ
  have hd0 : d ≠ 0 := by rintro rfl; simp at hd
  have hv := v_eq_ord hd0
  rw [hv] at hd
  have hpos : 0 < -Formalism.UG.ordL d := by
    rw [← WithZero.coe_one, WithZero.coe_lt_coe, ← ofAdd_zero, Multiplicative.ofAdd_lt] at hd; exact hd
  refine ⟨by omega, ?_⟩
  have h2 := v_inv_pow hϖ (-Formalism.UG.ordL d).toNat
  rw [Int.toNat_of_nonneg hpos.le, ← hv] at h2
  rw [map_mul, ← h2, ← map_mul, ← mul_pow, inv_mul_cancel₀ hϖ0, one_pow, map_one]

theorem main_gen (ϖ : L)
    (hϖ : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (n : ℕ) (b : Matrix (Fin n) (Fin n) L) :
    ∃ (r : ℕ) (M : Matrix (Fin n) (Fin r) L) (e : Fin r → ℕ),
    (∀ k, 1 ≤ e k) ∧ (∀ i k, M i k ∈ Formalism.UG.intL L) ∧ (∀ i k, (b * M) i k * ϖ ^ e k ∈ Formalism.UG.intL L) ∧
    (∀ m : Fin n → L, (∀ i, m i ∈ Formalism.UG.intL L) → ∃ α : Fin r → L, (∀ k, α k ∈ Formalism.UG.intL L) ∧
      ∀ i, (b *ᵥ (m - M *ᵥ α)) i ∈ Formalism.UG.intL L) ∧
    (∀ β : Fin r → L, (∀ k, β k ∈ Formalism.UG.intL L) → (∀ i, (b *ᵥ (M *ᵥ β)) i ∈ Formalism.UG.intL L) →
      ∀ k, Valued.v (β k) ≤ Valued.v ϖ ^ e k) := by
  classical
  obtain ⟨P, Q, ⟨hPi, P', hP'i, hPP'⟩, ⟨hQi, Q', hQ'i, hQQ'⟩, hD⟩ := exists_diag n n b
  have hP'P : P' * P = 1 := mul_eq_one_comm.mp hPP'
  obtain ⟨D, hDdef⟩ : ∃ D, D = P * b * Q := ⟨_, rfl⟩
  rw [← hDdef] at hD
  have hDd : ∀ i j, i ≠ j → D i j = 0 := fun i j h => hD i j (fun h' => h (Fin.ext h'))
  have hbQ : b * Q = P' * D := by
    rw [hDdef, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hP'P, Matrix.one_mul]
  obtain ⟨r, σ, hσinj, hσ⟩ : ∃ (r : ℕ) (σ : Fin r → Fin n), Function.Injective σ ∧
      ∀ j, (1 < Valued.v (D j j) ↔ ∃ k, σ k = j) := by
    let S := {i : Fin n // 1 < Valued.v (D i i)}
    refine ⟨Fintype.card S, fun k => ((Fintype.equivFin S).symm k).1,
      fun k l h => (Fintype.equivFin S).symm.injective (Subtype.ext h), fun j => ⟨fun h => ?_, ?_⟩⟩
    · exact ⟨Fintype.equivFin S ⟨j, h⟩, by simp⟩
    · rintro ⟨k, rfl⟩; exact ((Fintype.equivFin S).symm k).2
  have hσsel : ∀ k, 1 < Valued.v (D (σ k) (σ k)) := fun k => (hσ _).2 ⟨k, rfl⟩
  have hsum : ∀ g : Fin n → L, ∑ k, g (σ k) = ∑ j, if 1 < Valued.v (D j j) then g j else 0 := by
    intro g
    rw [← Finset.sum_filter, ← Finset.sum_image (hσinj.injOn)]
    congr 1; ext j; simp [hσ]
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin n) (Fin r) L, ∀ i k, M i k = Q i (σ k) :=
    ⟨Matrix.of fun i k => Q i (σ k), fun _ _ => rfl⟩
  have hbM : ∀ i k, (b * M) i k = P' i (σ k) * D (σ k) (σ k) := by
    intro i k
    have : (b * M) i k = (b * Q) i (σ k) := by simp only [Matrix.mul_apply, hM]
    rw [this, hbQ, Matrix.mul_apply, Finset.sum_eq_single (σ k)]
    · intro l _ hl; rw [hDd l (σ k) hl, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hPbM : ∀ j k, (P * b * M) j k = D j (σ k) := by
    intro j k; simp only [hDdef, Matrix.mul_apply, hM]
  refine ⟨r, M, fun k => (-Formalism.UG.ordL (D (σ k) (σ k))).toNat, fun k => (exp_of_gt hϖ (hσsel k)).1,
    fun i k => by rw [hM]; exact hQi _ _, fun i k => ?_, fun m hm => ?_, fun β hβ hbβ k => ?_⟩
  · rw [hbM, mem_intL, mul_assoc, map_mul, (exp_of_gt hϖ (hσsel k)).2, mul_one]
    exact mem_intL.1 (hP'i _ _)
  · obtain ⟨c, hc⟩ : ∃ c, c = Q' *ᵥ m := ⟨_, rfl⟩
    have hci : ∀ j, c j ∈ Formalism.UG.intL L := by rw [hc]; exact mulVec_int hQ'i hm
    have hmc : m = Q *ᵥ c := by rw [hc, Matrix.mulVec_mulVec, hQQ', Matrix.one_mulVec]
    obtain ⟨cs, hcs⟩ : ∃ cs : Fin n → L, ∀ j, cs j = if 1 < Valued.v (D j j) then c j else 0 :=
      ⟨fun j => if 1 < Valued.v (D j j) then c j else 0, fun _ => rfl⟩
    refine ⟨fun k => c (σ k), fun k => hci _, ?_⟩
    have hMα : M *ᵥ (fun k => c (σ k)) = Q *ᵥ cs := by
      funext i
      simp only [Matrix.mulVec, dotProduct, hM, hcs]
      exact (hsum (fun j => Q i j * c j)).trans (by simp only [mul_ite, mul_zero])
    rw [hmc, hMα, ← Matrix.mulVec_sub, Matrix.mulVec_mulVec, hbQ, ← Matrix.mulVec_mulVec]
    refine mulVec_int hP'i (fun j => ?_)
    have hDv : (D *ᵥ (c - cs)) j = D j j * (c j - cs j) := by
      simp only [Matrix.mulVec, dotProduct, Pi.sub_apply]
      rw [Finset.sum_eq_single j]
      · intro l _ hl; rw [hDd j l (Ne.symm hl), zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hDv, hcs]
    split_ifs with hj
    · rw [sub_self, mul_zero]; exact Subring.zero_mem _
    · rw [sub_zero]; exact Subring.mul_mem _ (mem_intL.2 (not_lt.1 hj)) (hci j)
  · have h1 := mulVec_int hPi hbβ (σ k)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec] at h1
    have h2 : ((P * b * M) *ᵥ β) (σ k) = D (σ k) (σ k) * β k := by
      simp only [Matrix.mulVec, dotProduct, hPbM]
      rw [Finset.sum_eq_single k]
      · intro l _ hl; rw [hDd _ _ (fun h => hl (hσinj h).symm), zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [h2, mem_intL] at h1
    have hex := (exp_of_gt hϖ (hσsel k)).2
    beta_reduce
    calc Valued.v (β k) = Valued.v (β k) * Valued.v (D (σ k) (σ k) * ϖ ^ (-Formalism.UG.ordL (D (σ k) (σ k))).toNat) := by
          rw [hex, mul_one]
      _ = Valued.v (D (σ k) (σ k) * β k) * Valued.v ϖ ^ (-Formalism.UG.ordL (D (σ k) (σ k))).toNat := by
          rw [map_mul, map_mul, map_pow]; ac_rfl
      _ ≤ Valued.v ϖ ^ (-Formalism.UG.ordL (D (σ k) (σ k))).toNat := mul_le_of_le_one_left' h1

end GlobalTheory.Hk3.SnfGen

theorem GlobalTheory.Hk3.snf_generators : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L), Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) →
  ∀ (n : ℕ) (a : GL (Fin n) L), ∃ (r : ℕ) (M : Matrix (Fin n) (Fin r) L) (e : Fin r → ℕ),
    (∀ k, 1 ≤ e k) ∧ (∀ i k, M i k ∈ Formalism.UG.intL L) ∧ (∀ i k, (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * M) i k * ϖ ^ e k ∈ Formalism.UG.intL L) ∧ (∀ m : Fin n → L, (∀ i, m i ∈ Formalism.UG.intL L) → ∃ α : Fin r → L, (∀ k, α k ∈ Formalism.UG.intL L) ∧
      ∀ i, (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ (m - M *ᵥ α)) i ∈ Formalism.UG.intL L) ∧ (∀ β : Fin r → L, (∀ k, β k ∈ Formalism.UG.intL L) → (∀ i, (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ (M *ᵥ β)) i ∈ Formalism.UG.intL L) →
      ∀ k, Valued.v (β k) ≤ Valued.v ϖ ^ e k) := by
  intro L _ _ ϖ hϖ n a
  exact GlobalTheory.Hk3.SnfGen.main_gen ϖ hϖ n _
