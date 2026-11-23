import Mathlib
open NumberField

namespace GlobalTheory
theorem norm_le_one_of_isIntegral_int_ultrametric {C : Type*} [NormedField C] [IsUltrametricDist C] {x : C} (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  have h := (Valuation.integer.integers (NormedField.valuation (K := C))).isIntegral_iff_v_le_one (x := x)
  have h2 : IsIntegral (NormedField.valuation (K := C)).integer x := hx.tower_top
  have h3 := h.1 h2
  rw [NormedField.valuation_apply] at h3
  exact_mod_cast h3

theorem norm_intCast_eq_one_of_prime_not_dvd_ultrametric {C : Type*} [NormedField C] [IsUltrametricDist C] {p : ℕ} (hp : p.Prime) (h : ‖(p : C)‖ < 1) {d : ℤ} (hd : ¬ p ∣ d.natAbs) : ‖(d : C)‖ = 1 := by
  have hc : IsCoprime (p : ℤ) d := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_eq_natAbs, Int.natAbs_natCast]
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 hd
  obtain ⟨u, v, huv⟩ := hc
  refine le_antisymm (IsUltrametricDist.norm_intCast_le_one C d) ?_
  by_contra hlt
  push_neg at hlt
  have h1 : (1 : C) = (u : C) * p + (v : C) * d := by exact_mod_cast congrArg (Int.cast : ℤ → C) huv.symm
  have h2 := IsUltrametricDist.norm_add_le_max ((u : C) * p) ((v : C) * d)
  rw [← h1, norm_one, norm_mul, norm_mul] at h2
  have hu := IsUltrametricDist.norm_intCast_le_one C u
  have hv := IsUltrametricDist.norm_intCast_le_one C v
  have a1 : ‖(u : C)‖ * ‖(p : C)‖ < 1 := mul_lt_one_of_nonneg_of_lt_one_right hu (norm_nonneg _) h
  have a2 : ‖(v : C)‖ * ‖(d : C)‖ < 1 := mul_lt_one_of_nonneg_of_lt_one_right hv (norm_nonneg _) hlt
  exact absurd h2 (not_le.2 (max_lt a1 a2))

open Classical in

theorem sum_adjugate_traceMatrix_embeddings (E : Type) [Field E] [NumberField E]
    (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosed Ω] (σ φ : E →ₐ[ℚ] Ω) :
    ∑ j, (∑ k, ((Algebra.traceMatrix ℤ (RingOfIntegers.basis E)).adjugate j k : Ω)
        * σ (RingOfIntegers.basis E k : E)) * φ (RingOfIntegers.basis E j : E)
      = if φ = σ then (discr E : Ω) else 0 := by
  set G := Algebra.traceMatrix ℤ (RingOfIntegers.basis E) with hG
  set M := Algebra.embeddingsMatrix ℚ Ω (integralBasis E) with hM
  have hD : (discr E : Ω) ≠ 0 := by exact_mod_cast discr_ne_zero E
  have h1 : G.map (Int.castRingHom Ω) = M * M.transpose := by
    rw [hM, ← Algebra.traceMatrix_eq_embeddingsMatrix_mul_trans]
    ext i j
    simp only [hG, Matrix.map_apply, Algebra.traceMatrix_apply, Algebra.traceForm_apply,
      integralBasis_apply, ← map_mul, eq_intCast]
    have := Algebra.coe_trace_int (RingOfIntegers.basis E i * RingOfIntegers.basis E j)
    rw [RingOfIntegers.coe_eq_algebraMap] at this
    rw [← this, map_intCast]
  have hdet : G.det = discr E := by
    rw [hG, ← Algebra.discr_def]
  have h2 : G.adjugate.map (Int.castRingHom Ω) * G.map (Int.castRingHom Ω)
      = (discr E : Ω) • (1 : Matrix _ _ Ω) := by
    rw [← Matrix.map_mul, Matrix.adjugate_mul, hdet]
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite,
      mul_one, mul_zero, apply_ite (Int.castRingHom Ω), map_zero, eq_intCast]
  have h3 : ((discr E : Ω)⁻¹ • (G.adjugate.map (Int.castRingHom Ω) * M)) * M.transpose = 1 := by
    rw [Matrix.smul_mul, Matrix.mul_assoc, ← h1, h2, smul_smul, inv_mul_cancel₀ hD, one_smul]
  have e : Module.Free.ChooseBasisIndex ℤ (𝓞 E) ≃ (E →ₐ[ℚ] Ω) :=
    Fintype.equivOfCardEq (by
      rw [AlgHom.card, Module.finrank_eq_card_basis (integralBasis E)])
  have h4 := (Matrix.mul_eq_one_comm_of_equiv e).1 h3
  have h5 : M.transpose * (G.adjugate.map (Int.castRingHom Ω) * M) = (discr E : Ω) • 1 := by
    rw [← h4, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hD, one_smul]
  have h6 := congrFun (congrFun h5 φ) σ
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, hM,
    Algebra.embeddingsMatrix_apply, integralBasis_apply, eq_intCast, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero] at h6
  rw [← h6]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem exists_integral_idempotent_of_not_dvd_discr :
    ∀ (E : Type) [Field E] [NumberField E] (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] (p : ℕ), p.Prime → ‖(p : C)‖ < 1 → ¬ p ∣ (NumberField.discr E).natAbs → ∀ σ : E →+* C, ∃ (n : ℕ) (a : Fin n → 𝓞 E) (c : Fin n → C), (∀ j, ‖c j‖ ≤ 1) ∧ ∑ j, c j * σ (a j : E) = 1 ∧ ∀ φ : E →+* C, φ ≠ σ → ∑ j, c j * φ (a j : E) = 0 := by
  classical
  intro E _ _ C _ _ p hp hpn hd σ
  haveI : CharZero C := σ.charZero_iff σ.injective |>.1 inferInstance
  have hD1 : ‖(discr E : C)‖ = 1 := norm_intCast_eq_one_of_prime_not_dvd_ultrametric hp hpn hd
  have hD : (discr E : C) ≠ 0 := by exact_mod_cast discr_ne_zero E
  set b := RingOfIntegers.basis E with hb
  set G := Algebra.traceMatrix ℤ b with hG
  let c : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → C :=
    fun j => (discr E : C)⁻¹ * ∑ k, (G.adjugate j k : C) * σ (b k : E)
  have key : ∀ φ : E →+* C, ∑ j, c j * φ (b j : E) = if φ = σ then 1 else 0 := by
    intro φ
    let ι : C →+* AlgebraicClosure C := algebraMap _ _
    have h := sum_adjugate_traceMatrix_embeddings E (AlgebraicClosure C)
      (ι.comp σ).toRatAlgHom (ι.comp φ).toRatAlgHom
    have hiff : (ι.comp φ).toRatAlgHom = (ι.comp σ).toRatAlgHom ↔ φ = σ := by
      constructor
      · intro hh
        ext x
        exact ι.injective (DFunLike.congr_fun hh x)
      · rintro rfl; rfl
    have h' : ∑ j, (∑ k, (G.adjugate j k : C) * σ (b k : E)) * φ (b j : E)
        = if φ = σ then (discr E : C) else 0 := by
      apply ι.injective
      simp only [hiff] at h
      simp only [map_sum, map_mul, map_intCast, apply_ite ι, map_zero]
      convert h using 2
      rfl
    simp only [c, mul_assoc, ← Finset.mul_sum, h']
    split_ifs
    · exact inv_mul_cancel₀ hD
    · exact mul_zero _
  let e := (Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))).symm
  refine ⟨_, fun j => b (e j), fun j => c (e j), fun j => ?_, ?_, fun φ hφ => ?_⟩
  · simp only [c]
    rw [norm_mul, norm_inv, hD1, inv_one, one_mul]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
    rw [norm_mul]
    refine mul_le_one₀ (IsUltrametricDist.norm_intCast_le_one C _) (norm_nonneg _) ?_
    exact norm_le_one_of_isIntegral_int_ultrametric
      ((RingOfIntegers.isIntegral_coe (b k)).map σ.toIntAlgHom)
  · rw [e.sum_comp (fun j => c j * σ (b j : E)), key, if_pos rfl]
  · rw [e.sum_comp (fun j => c j * φ (b j : E)), key, if_neg hφ]
end GlobalTheory
