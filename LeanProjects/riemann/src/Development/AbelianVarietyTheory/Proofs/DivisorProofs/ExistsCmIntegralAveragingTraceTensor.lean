import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsStarNormLEOfIsCMField

set_option autoImplicit false

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc
open NumberField

namespace GlobalTheory

namespace TraceTensor

variable {E : Type} [Field E] [NumberField E]

theorem exists_integral_orthogonal (σ : E ≃ₐ[ℚ] E) (hσ : ∀ x, σ (σ x) = x) :
    ∃ (n : ℕ) (b : Fin n → 𝓞 E) (e : Module.Basis (Fin n) ℚ E), (∀ i, e i = (b i : E)) ∧
      ∀ i j, i ≠ j → Algebra.trace ℚ E (σ (e i) * e j) = 0 := by
  classical
  let B : LinearMap.BilinForm ℚ E := (Algebra.traceForm ℚ E).comp σ.toLinearMap LinearMap.id
  have hB : ∀ x y, B x y = Algebra.trace ℚ E (σ x * y) := fun _ _ => rfl
  have hs : LinearMap.IsSymm B := ⟨fun x y => by
    rw [RingHom.id_apply, hB, hB, ← Algebra.trace_eq_of_algEquiv σ, map_mul, hσ, mul_comm]⟩
  obtain ⟨e, he⟩ := LinearMap.BilinForm.exists_orthogonal_basis hs
  have hint : ∀ y : E, ∃ (m : ℕ) (b : 𝓞 E), m ≠ 0 ∧ (m : ℚ) • y = (b : E) := by
    intro y
    have halg : IsAlgebraic ℤ y :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic y)
    obtain ⟨m, b, hm, hb⟩ := halg.exists_nsmul_eq (S := 𝓞 E)
    exact ⟨m, b, hm, by rw [Nat.cast_smul_eq_nsmul, hb]⟩
  choose m b hm hb using hint
  have hu : ∀ i, IsUnit ((m (e i) : ℕ) : ℚ) := fun i => IsUnit.mk0 _ (Nat.cast_ne_zero.2 (hm _))
  refine ⟨_, fun i => b (e i), e.isUnitSMul hu, fun i => ?_, fun i j hij => ?_⟩
  · rw [Module.Basis.isUnitSMul_apply, hb]
  · have h : Algebra.trace ℚ E (σ (e i) * e j) = 0 := he hij
    rw [Module.Basis.isUnitSMul_apply, Module.Basis.isUnitSMul_apply, Rat.smul_def (m (e i) : ℚ), map_mul σ,
      map_ratCast, ← Rat.smul_def, smul_mul_assoc,
      mul_smul_comm, map_smul, map_smul, h, smul_zero, smul_zero]

theorem trace_mul_eq_repr (σ : E ≃ₐ[ℚ] E) {ι : Type} [Fintype ι] (e : Module.Basis ι ℚ E)
    (ho : ∀ i j, i ≠ j → Algebra.trace ℚ E (σ (e i) * e j) = 0) (y : E) (i : ι) :
    Algebra.trace ℚ E (σ (e i) * y) = e.repr y i * Algebra.trace ℚ E (σ (e i) * e i) := by
  conv_lhs => rw [← e.sum_repr y, Finset.mul_sum, map_sum]
  rw [Finset.sum_eq_single i]
  · rw [mul_smul_comm, map_smul, smul_eq_mul]
  · intro j _ hj
    rw [mul_smul_comm, map_smul, ho i j hj.symm, smul_zero]
  · simp

end TraceTensor

open TraceTensor in

theorem exists_cm_trace_tensor : ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E), ∃ (n c : ℕ) (b : Fin n → NumberField.RingOfIntegers E) (T : Matrix (Fin n) (Fin n) ℤ), 0 < c ∧ (∀ s t, T s t = T t s) ∧ (∀ (a : NumberField.RingOfIntegers E) (g : NumberField.RingOfIntegers E →ₗ[ℤ] NumberField.RingOfIntegers E →ₗ[ℤ] ℤ), ∑ s, ∑ t, T s t * g (b s * a) (b t) = ∑ s, ∑ t, T s t * g (b s) (b t * H.bar a)) ∧ ∑ s, ∑ t, T s t • (H.bar (b s) * b t) = (c : NumberField.RingOfIntegers E) ∧ ∀ v : Fin n → ℤ, v ≠ 0 → 0 < ∑ s, ∑ t, T s t * v s * v t := by
  intro E _ _ _ H
  classical
  let σ : E ≃ₐ[ℚ] E := (IsCMField.complexConj E).restrictScalars ℚ
  have hσσ : ∀ x, σ (σ x) = x := fun x => IsCMField.complexConj_apply_apply E x
  have hbar : ∀ x : 𝓞 E, ((H.bar x : 𝓞 E) : E) = σ (x : E) := fun x => H.bar_eq x
  obtain ⟨n, b, e, heb, ho⟩ := exists_integral_orthogonal σ hσσ
  have htr : ∀ x y : 𝓞 E, ((Algebra.trace ℤ (𝓞 E) (H.bar x * y) : ℤ) : ℚ)
      = Algebra.trace ℚ E (σ (x : E) * (y : E)) := by
    intro x y
    rw [Algebra.coe_trace_int, ← hbar]
    rfl
  let d : Fin n → ℤ := fun i => Algebra.trace ℤ (𝓞 E) (H.bar (b i) * b i)
  have hdq : ∀ i, (d i : ℚ) = Algebra.trace ℚ E (σ (e i) * e i) := fun i => by
    rw [heb]; exact htr _ _
  have hdq0 : ∀ i, 0 < Algebra.trace ℚ E (σ (e i) * e i) := fun i =>
    StarNormBound.trace_conj_mul_pos _ (e.ne_zero i)
  have hd : ∀ i, 0 < d i := fun i => by
    have := hdq0 i
    rw [← hdq] at this
    exact_mod_cast this
  let t : Fin n → ℤ := fun i => ∏ j ∈ Finset.univ.erase i, d j
  let C : ℤ := ∏ j, d j
  have hC : 0 < C := Finset.prod_pos fun j _ => hd j
  have ht : ∀ i, 0 < t i := fun i => Finset.prod_pos fun j _ => hd j
  have htd : ∀ i, d i * t i = C := fun i => Finset.mul_prod_erase _ _ (Finset.mem_univ i)
  have htq : ∀ i, (t i : ℚ) = C * (Algebra.trace ℚ E (σ (e i) * e i))⁻¹ := fun i => by
    rw [← hdq, ← htd i]
    have : (d i : ℚ) ≠ 0 := by exact_mod_cast (hd i).ne'
    push_cast
    field_simp
  have hexp : ∀ x : 𝓞 E, C • x = ∑ j, (t j * Algebra.trace ℤ (𝓞 E) (H.bar (b j) * x)) • b j := by
    intro x
    apply RingOfIntegers.coe_injective
    rw [map_zsmul, map_sum]
    have hx := e.sum_repr (x : E)
    change C • (x : E) = _
    conv_lhs => rw [← hx, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul]
    change _ = _ • (b j : E)
    rw [← heb, ← Int.cast_smul_eq_zsmul ℚ, ← Int.cast_smul_eq_zsmul ℚ, smul_smul]
    congr 1
    rw [Int.cast_mul, htr, ← heb, trace_mul_eq_repr σ e ho, htq]
    have := (hdq0 j).ne'
    field_simp
  have hsym : ∀ x y a : 𝓞 E, Algebra.trace ℤ (𝓞 E) (H.bar x * (y * H.bar a))
      = Algebra.trace ℤ (𝓞 E) (H.bar y * (x * a)) := by
    intro x y a
    have : ((Algebra.trace ℤ (𝓞 E) (H.bar x * (y * H.bar a)) : ℤ) : ℚ)
      = ((Algebra.trace ℤ (𝓞 E) (H.bar y * (x * a)) : ℤ) : ℚ) := by
      rw [htr, htr, ← Algebra.trace_eq_of_algEquiv σ]
      congr 1
      have h1 : ((y * H.bar a : 𝓞 E) : E) = (y : E) * σ (a : E) := by rw [← hbar]; rfl
      have h2 : ((x * a : 𝓞 E) : E) = (x : E) * (a : E) := rfl
      rw [h1, h2, map_mul, map_mul, hσσ, hσσ]
      ring
    exact_mod_cast this
  refine ⟨n, C.toNat, b, Matrix.diagonal t, by omega, fun s u => ?_, fun a g => ?_, ?_, fun v hv => ?_⟩
  · by_cases h : s = u
    · rw [h]
    · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h)]
  · simp only [Matrix.diagonal_apply, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    apply mul_left_cancel₀ hC.ne'
    have h1 : ∀ i, C * (t i * g (b i * a) (b i)) =
        ∑ j, t i * (t j * Algebra.trace ℤ (𝓞 E) (H.bar (b j) * (b i * a))) * g (b j) (b i) := by
      intro i
      have : C * g (b i * a) (b i) = g (C • (b i * a)) (b i) := by
        rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
      rw [mul_left_comm, this, hexp, map_sum, LinearMap.sum_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
      ring
    have h2 : ∀ j, C * (t j * g (b j) (b j * H.bar a)) =
        ∑ i, t i * (t j * Algebra.trace ℤ (𝓞 E) (H.bar (b j) * (b i * a))) * g (b j) (b i) := by
      intro j
      have : C * g (b j) (b j * H.bar a) = g (b j) (C • (b j * H.bar a)) := by
        rw [map_smul, smul_eq_mul]
      rw [mul_left_comm, this, hexp, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, smul_eq_mul, hsym]
      ring
    rw [Finset.mul_sum, Finset.mul_sum]
    simp only [h1, h2]
    exact Finset.sum_comm
  · simp only [Matrix.diagonal_apply, ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have hc := StarNormBound.casimir σ e ho fun i => (hdq0 i).ne'
    apply RingOfIntegers.coe_injective
    rw [map_sum, map_natCast, ← Int.cast_natCast, Int.toNat_of_nonneg hC.le, ← mul_one (C : E), ← hc,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, map_mul]
    change t i • (((H.bar (b i) : 𝓞 E) : E) * (b i : E)) = _
    rw [hbar, ← heb, ← Int.cast_smul_eq_zsmul ℚ, htq, mul_smul, Int.cast_smul_eq_zsmul, zsmul_eq_mul]
  · simp only [Matrix.diagonal_apply, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hv
    refine Finset.sum_pos' (fun j _ => ?_) ⟨i, Finset.mem_univ _, ?_⟩
    · rw [mul_assoc]; exact mul_nonneg (ht j).le (mul_self_nonneg _)
    · rw [mul_assoc]; exact mul_pos (ht i) (mul_self_pos.2 hi)

end GlobalTheory
