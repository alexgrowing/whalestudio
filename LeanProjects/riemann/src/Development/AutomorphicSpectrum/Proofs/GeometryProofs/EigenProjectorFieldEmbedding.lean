import Mathlib

open NumberField Module

namespace GlobalTheory.CompanionTheory.TraceProj

theorem injective_of_charZero (E : Type) [Field E] [NumberField E] (K : Type) [Field K] [CharZero K]
    (σ : 𝓞 E →+* K) : Function.Injective σ := by
  refine (RingHom.injective_iff_ker_eq_bot σ).mpr (Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_)
  rw [eq_bot_iff]
  intro n hn
  rw [Ideal.mem_comap, RingHom.mem_ker, eq_intCast, map_intCast, Int.cast_eq_zero] at hn
  rw [Ideal.mem_bot]
  exact hn

theorem sum_repr_smul_dual (E : Type) [Field E] [NumberField E] {ι : Type} [Fintype ι]
    [DecidableEq ι] (b : Basis ι ℤ (𝓞 E)) (B D : Basis ι ℚ E)
    (hB : ∀ i, B i = algebraMap (𝓞 E) E (b i))
    (hD : ∀ i j, Algebra.traceForm ℚ E (D j) (B i) = if i = j then 1 else 0)
    (hrepr : ∀ (x : E) (k : ι), D.repr x k = Algebra.traceForm ℚ E x (B k))
    (a : 𝓞 E) (l : ι) :
    ∑ k, ((b.repr (a * b k) l : ℤ) : E) * D k = algebraMap (𝓞 E) E a * D l := by
  have hB' : ∀ k, algebraMap (𝓞 E) E a * B k = ∑ i, ((b.repr (a * b k) i : ℤ) : E) * B i := by
    intro k
    rw [hB k, ← map_mul]
    conv_lhs => rw [← b.sum_repr (a * b k)]
    simp [map_sum, hB, zsmul_eq_mul]
  have hterm : ∀ k i, Algebra.trace ℚ E (D l * (((b.repr (a * b k) i : ℤ) : E) * B i)) =
      (b.repr (a * b k) i : ℚ) * (if i = l then 1 else 0) := by
    intro k i
    rw [← hD i l, Algebra.traceForm_apply, mul_left_comm,
      show (((b.repr (a * b k) i : ℤ) : E)) * (D l * B i) =
        (b.repr (a * b k) i : ℚ) • (D l * B i) by rw [Rat.smul_def]; push_cast; rfl,
      LinearMap.map_smul, smul_eq_mul]
  have hcoord : ∀ k, D.repr (algebraMap (𝓞 E) E a * D l) k = (b.repr (a * b k) l : ℚ) := by
    intro k
    rw [hrepr, Algebra.traceForm_apply, mul_comm (algebraMap (𝓞 E) E a) (D l), mul_assoc, hB' k,
      Finset.mul_sum, map_sum]
    simp only [hterm, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  calc ∑ k, ((b.repr (a * b k) l : ℤ) : E) * D k
      = ∑ k, D.repr (algebraMap (𝓞 E) E a * D l) k • D k := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hcoord, Rat.smul_def]
        push_cast
        rfl
    _ = algebraMap (𝓞 E) E a * D l := D.sum_repr _

theorem exists_coeff (E : Type) [Field E] [NumberField E] (K : Type) [Field K] [CharZero K]
    (σ : 𝓞 E →+* K) {ι : Type} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ (𝓞 E)) (B : Basis ι ℚ E)
    (hB : ∀ i, B i = algebraMap (𝓞 E) E (b i)) :
    ∃ c : ι → K, ∑ k, c k * σ (b k) = 1 ∧
      ∀ (a : 𝓞 E) (l : ι), ∑ k, ((b.repr (a * b k) l : ℤ) : K) * c k = σ a * c l := by
  have hnd := traceForm_nondegenerate ℚ E
  let D := (Algebra.traceForm ℚ E).dualBasis hnd B
  have hD : ∀ i j, Algebra.traceForm ℚ E (D j) (B i) = if i = j then 1 else 0 := fun i j =>
    LinearMap.BilinForm.apply_dualBasis_left hnd B j i
  have hrepr : ∀ (x : E) (k : ι), D.repr x k = Algebra.traceForm ℚ E x (B k) := fun x k =>
    LinearMap.BilinForm.dualBasis_repr_apply hnd B x k
  let σ' : E →+* K := IsFractionRing.lift (injective_of_charZero E K σ)
  have hσ' : ∀ x, σ' (algebraMap (𝓞 E) E x) = σ x := IsFractionRing.lift_algebraMap _
  have h1 : ∑ k, D k * B k = 1 := by
    have h0 : ∑ k, D k * B k - 1 = 0 := by
      refine hnd.1 _ fun x => ?_
      rw [Algebra.traceForm_apply, sub_mul, one_mul, map_sub, sub_eq_zero, Finset.sum_mul, map_sum,
        Algebra.trace_eq_matrix_trace D x, Matrix.trace]
      simp only [Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul, hrepr, Algebra.traceForm_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring_nf
    exact sub_eq_zero.mp h0
  refine ⟨fun k => σ' (D k), ?_, fun a l => ?_⟩
  · calc ∑ k, σ' (D k) * σ (b k) = σ' (∑ k, D k * B k) := by simp [map_sum, hB, hσ']
      _ = 1 := by rw [h1, map_one]
  · have h := congrArg σ' (sum_repr_smul_dual E b B D hB hD hrepr a l)
    simpa [map_sum, map_mul, hσ'] using h

theorem exists_eigen_projector : ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] [CharZero K]
    (σ : 𝓞 E →+* K), ∃ (n : ℕ) (e : Fin n → 𝓞 E) (c : Fin n → K), ∑ k, c k * σ (e k) = 1 ∧
      ∀ (L W : Type) [Field L] [AddCommGroup W] [Module L W] (j : K →+* L)
        (ρ : 𝓞 E →+* Module.End L W) (a : 𝓞 E) (w : W),
        ρ a (∑ k, j (c k) • ρ (e k) w) = j (σ a) • ∑ k, j (c k) • ρ (e k) w := by
  intro E _ _ K _ _ σ
  classical
  let b := RingOfIntegers.basis E
  obtain ⟨c, hc1, hc2⟩ := exists_coeff E K σ b (integralBasis E) (fun i => integralBasis_apply E i)
  let eqv := Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))
  refine ⟨_, fun k => b (eqv.symm k), fun k => c (eqv.symm k), ?_, ?_⟩
  · rw [← hc1]
    exact Equiv.sum_comp eqv.symm (fun i => c i * σ (b i))
  · intro L W _ _ _ j ρ a w
    rw [Equiv.sum_comp eqv.symm (fun i => j (c i) • ρ (b i) w)]
    have hmul : ∀ i, ρ a (ρ (b i) w) = ∑ l, ((b.repr (a * b i) l : ℤ) : L) • ρ (b l) w := by
      intro i
      rw [← Module.End.mul_apply, ← map_mul]
      conv_lhs => rw [← b.sum_repr (a * b i)]
      simp [map_sum, LinearMap.sum_apply, Int.cast_smul_eq_zsmul]
    have hj : ∀ l, ∑ i, j (c i) * ((b.repr (a * b i) l : ℤ) : L) = j (σ a) * j (c l) := by
      intro l
      have h := congrArg j (hc2 a l)
      simp only [map_sum, map_mul, map_intCast] at h
      rw [← h]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    simp only [map_sum, map_smul, hmul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Finset.sum_smul, hj l]

end GlobalTheory.CompanionTheory.TraceProj
