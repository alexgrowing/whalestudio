import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AdelicLattices₂.AlgebraMapNormOfBasisOneSqrt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor

open NumberField IsDedekindDomain
open scoped Matrix WithZero

namespace GlobalTheory.LocalQuad

section Algebra

variable {k : Type*} [Field k]

theorem exists_norm_of_quaternary [CharZero k] {α β γ s : k} (hα : α ≠ 0) (hβ : β ≠ 0) (hγ : γ ≠ 0)
    (hs : s ^ 2 = α * β * γ) {x y z t : k} (h0 : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0 ∨ t ≠ 0)
    (h : x ^ 2 - α * y ^ 2 - β * z ^ 2 + γ * t ^ 2 = 0) : ∃ X Y : k, β = X ^ 2 - α * Y ^ 2 := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact mul_ne_zero (mul_ne_zero hα hβ) hγ (by simpa using hs.symm)
  obtain ⟨u, hu⟩ : ∃ u, u = t * s / (α * β) := ⟨_, rfl⟩
  have hu2 : α * β * u ^ 2 = γ * t ^ 2 := by
    rw [hu, div_pow, mul_pow, hs]; field_simp
  have h1 : x ^ 2 - α * y ^ 2 = β * (z ^ 2 - α * u ^ 2) := by linear_combination h + hu2
  by_cases hD : z ^ 2 - α * u ^ 2 = 0
  · refine GlobalTheory.Published.HasseNormSt.of_isSquare hα ?_ β
    by_cases hu0 : u = 0
    · have hz : z = 0 := by simpa [hu0] using hD
      have ht : t = 0 := by
        have : γ * t ^ 2 = 0 := by rw [← hu2, hu0]; ring
        simpa [hγ] using this
      have hxy : x ^ 2 = α * y ^ 2 := by linear_combination h1 + β * hD
      have hy : y ≠ 0 := by
        rintro rfl
        have hx : x = 0 := by simpa using hxy
        simp [hx, hz, ht] at h0
      exact ⟨x / y, by field_simp; linear_combination -hxy⟩
    · exact ⟨z / u, by field_simp; linear_combination -hD⟩
  · refine ⟨(x * z + α * y * u) / (z ^ 2 - α * u ^ 2), (x * u + y * z) / (z ^ 2 - α * u ^ 2), ?_⟩
    field_simp
    linear_combination (-(z ^ 2 - α * u ^ 2)) * h1

theorem exists_quaternary_of_coordinates {α β γ : k} (hα : α ≠ 0) (hβ : β ≠ 0)
    {X₀ X₁ Y₀ Y₁ : k}
    (h1 : β = X₀ ^ 2 + α * β * γ * X₁ ^ 2 - α * (Y₀ ^ 2 + α * β * γ * Y₁ ^ 2))
    (h2 : X₀ * X₁ = α * (Y₀ * Y₁)) :
    ∃ x y z t : k, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0 ∨ t ≠ 0) ∧
      x ^ 2 - α * y ^ 2 - β * z ^ 2 + γ * t ^ 2 = 0 := by
  by_cases hw : X₁ ^ 2 - α * Y₁ ^ 2 = 0
  · exact ⟨X₀, Y₀, 1, 0, by simp, by linear_combination -h1 - α * β * γ * hw⟩
  · refine ⟨-Y₁ * (α * β), -X₁ * β, -(X₀ * Y₁ - Y₀ * X₁) * α, (X₁ ^ 2 - α * Y₁ ^ 2) * (α * β),
      Or.inr (Or.inr (Or.inr (mul_ne_zero hw (mul_ne_zero hα hβ)))), ?_⟩
    linear_combination (-(α * β * (X₁ ^ 2 - α * Y₁ ^ 2))) * h1 - α * β * (X₀ * X₁ - α * (Y₀ * Y₁)) * h2

theorem isotropic_four_iff {a : Fin 4 → k} (ha : a 0 ≠ 0) :
    (∃ x : Fin 4 → k, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0) ↔
      ∃ x y z t : k, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0 ∨ t ≠ 0) ∧
        x ^ 2 - (-(a 0 * a 1)) * y ^ 2 - (-(a 0 * a 2)) * z ^ 2 + (a 0 * a 3) * t ^ 2 = 0 := by
  constructor
  · rintro ⟨x, hx, h⟩
    rw [Fin.sum_univ_four] at h
    refine ⟨a 0 * x 0, x 1, x 2, x 3, ?_, by linear_combination a 0 * h⟩
    by_contra hc
    push Not at hc
    obtain ⟨h0, h1, h2, h3⟩ := hc
    apply hx
    funext i
    fin_cases i
    · simpa [ha] using h0
    · exact h1
    · exact h2
    · exact h3
  · rintro ⟨x, y, z, t, hx, h⟩
    refine ⟨![x / a 0, y, z, t], ?_, ?_⟩
    · intro hc
      have h0 := congrFun hc 0
      have h1 := congrFun hc 1
      have h2 := congrFun hc 2
      have h3 := congrFun hc 3
      simp [ha] at h0 h1 h2 h3
      simp [h0, h1, h2, h3] at hx
    · rw [Fin.sum_univ_four]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      field_simp
      linear_combination h

theorem isotropic_succ_iff {n : ℕ} {a : Fin (n + 1) → k} :
    (∃ x : Fin (n + 1) → k, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0) ↔
      ∃ (t : k) (z : Fin n → k), (t ≠ 0 ∨ z ≠ 0) ∧ a 0 * t ^ 2 + ∑ i, a i.succ * z i ^ 2 = 0 := by
  constructor
  · rintro ⟨x, hx, h⟩
    rw [Fin.sum_univ_succ] at h
    refine ⟨x 0, fun i => x i.succ, ?_, h⟩
    by_contra hc
    push Not at hc
    apply hx
    funext i
    refine Fin.cases hc.1 (fun j => congrFun hc.2 j) i
  · rintro ⟨t, z, hx, h⟩
    refine ⟨Fin.cons t z, ?_, by simpa [Fin.sum_univ_succ] using h⟩
    intro hc
    rcases hx with hx | hx
    · exact hx (by simpa using congrFun hc 0)
    · exact hx (funext fun i => by simpa using congrFun hc i.succ)

theorem exists_value_isotropic [CharZero k] {n : ℕ} {a a' : k} (ha : a ≠ 0) (ha' : a' ≠ 0)
    {b : Fin (n + 1) → k} (hb : b 0 ≠ 0) {x y : k} {z : Fin (n + 1) → k}
    (h0 : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) (h : a * x ^ 2 + (a' * y ^ 2 + ∑ i, b i * z i ^ 2) = 0) :
    ∃ x y : k, a * x ^ 2 + a' * y ^ 2 ≠ 0 ∧ ∀ μ : k, IsSquare (μ / (a * x ^ 2 + a' * y ^ 2)) →
      ∃ (t : k) (z : Fin (n + 1) → k), (t ≠ 0 ∨ z ≠ 0) ∧ μ * t ^ 2 + ∑ i, b i * z i ^ 2 = 0 := by
  have key : ∀ ν : k, ν ≠ 0 → ∀ z : Fin (n + 1) → k, ν + ∑ i, b i * z i ^ 2 = 0 →
      ∀ μ : k, IsSquare (μ / ν) →
      ∃ (t : k) (z : Fin (n + 1) → k), (t ≠ 0 ∨ z ≠ 0) ∧ μ * t ^ 2 + ∑ i, b i * z i ^ 2 = 0 := by
    rintro ν hν z hz μ ⟨s, hs⟩
    refine ⟨1, fun i => s * z i, Or.inl one_ne_zero, ?_⟩
    have : ∑ i, b i * (s * z i) ^ 2 = s ^ 2 * ∑ i, b i * z i ^ 2 := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [div_eq_iff hν] at hs
    rw [this, hs]
    linear_combination s ^ 2 * hz
  by_cases hμ : a * x ^ 2 + a' * y ^ 2 = 0
  · by_cases hz : z = 0
    · have hy : y ≠ 0 := by
        rintro rfl
        have hx : x = 0 := by simpa [ha] using hμ
        simp [hx, hz] at h0
      obtain ⟨X, Y, hXY⟩ := GlobalTheory.Published.HasseNormSt.of_isSquare (δ := -a' / a) (by simp [ha, ha'])
        ⟨x / y, by field_simp; linear_combination -hμ⟩ (-b 0 / a)
      have e : a * X ^ 2 + a' * Y ^ 2 = -b 0 := by
        field_simp at hXY
        linear_combination -hXY
      refine ⟨X, Y, by rw [e]; exact neg_ne_zero.2 hb, key _ (by rw [e]; exact neg_ne_zero.2 hb)
        (Pi.single 0 1) ?_⟩
      rw [e, Fin.sum_univ_succ]
      simp
    · refine ⟨1, 0, by simpa using ha, fun μ _ => ⟨0, z, Or.inr hz, ?_⟩⟩
      linear_combination h - hμ
  · exact ⟨x, y, hμ, key _ hμ z (by linear_combination h)⟩

theorem isotropic_of_injective {ι κ : Type*} [Fintype ι] [Fintype κ] (e : κ → ι)
    (he : Function.Injective e) {a : ι → k}
    (h : ∃ x : κ → k, x ≠ 0 ∧ ∑ j, a (e j) * x j ^ 2 = 0) :
    ∃ x : ι → k, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0 := by
  classical
  obtain ⟨x, hx, h⟩ := h
  refine ⟨Function.extend e x 0, fun hc => hx (funext fun j => ?_), ?_⟩
  · simpa [he.extend_apply] using congrFun hc (e j)
  · rw [← h]
    symm
    refine Finset.sum_of_injOn e he.injOn (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) ?_ ?_
    · intro i _ hi
      rw [Function.extend_apply' _ _ _ (by simpa using hi)]
      simp
    · intro j _
      rw [he.extend_apply]

theorem isotropic_real {ι : Type*} [Fintype ι] {a : ι → ℝ} {i j : ι} (hi : a i < 0) (hj : 0 < a j) :
    ∃ x : ι → ℝ, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0 := by
  have hij : i ≠ j := by rintro rfl; linarith
  refine isotropic_of_injective ![i, j] ?_ ⟨![√(a j), √(-a i)], ?_, ?_⟩
  · intro p q h
    fin_cases p <;> fin_cases q <;> simp_all [eq_comm]
  · intro hc
    have := congrFun hc 0
    simp only [Matrix.cons_val_zero, Pi.zero_apply] at this
    exact (Real.sqrt_pos.2 hj).ne' this
  · rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [Real.sq_sqrt hj.le, Real.sq_sqrt (by linarith)]
    ring

end Algebra

end GlobalTheory.LocalQuad
