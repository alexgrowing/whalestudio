import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock

open Matrix MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil ValuativeRel
open scoped Pointwise

noncomputable section
namespace GlobalTheory.SplitFlip.FourierDepth

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A D : Type*} [DecidableEq D]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem setCols_add (P : Finset D) (Y Z : Matrix A D k) (T : Matrix A P k) :
    setCols P (Y + Z) T = setCols P Y T + setCols P Z 0 := by
  ext i j
  by_cases h : j ∈ P <;> simp [setCols, h]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [DecidableEq D] in

theorem pairCols_add [Fintype A] (P : Finset D) (Y Z : Matrix A D k) (T : Matrix A P k) :
    pairCols P (Y + Z) T = pairCols P Y T + pairCols P Z T := by
  simp [pairCols, mul_add, Finset.sum_add_distrib]

omit [DecidableEq D] in

theorem mem_matLat_diagLat {c : D → kˣ} {X : Matrix A D k} :
    X ∈ matLat A (diagLat c) ↔ ∀ i j, valuation k (X i j) ≤ valuation k (c j : k) := Iff.rfl

omit [DecidableEq D] in

theorem mem_matLat_smul_stdLat {c : kˣ} {X : Matrix A D k} :
    X ∈ matLat A (c • stdLat k D) ↔ ∀ i j, valuation k (X i j) ≤ valuation k (c : k) := by
  rw [stdLat, smul_diagLat, mem_matLat_diagLat]
  simp

theorem mem_matLat_blockLat {ϖ : kˣ} {e : ℕ} {P : Finset D} {X : Matrix A D k} :
    X ∈ matLat A (blockLat ϖ e P) ↔
      (∀ i, ∀ j ∈ P, ((ϖ ^ e : kˣ) : k) * X i j ∈ 𝒪[k]) ∧ ∀ i, ∀ j ∉ P, X i j ∈ 𝒪[k] := by
  have h0 : 0 < valuation k ((ϖ ^ e : kˣ) : k) := zero_lt_iff.2 (by simp)
  have h1 : ∀ x : k, ((ϖ ^ e : kˣ) : k) * x ∈ 𝒪[k] ↔
      valuation k x ≤ valuation k (((ϖ ^ e)⁻¹ : kˣ) : k) := fun x => by
    rw [Valuation.mem_integer_iff, map_mul, Units.val_inv_eq_inv_val, map_inv₀, mul_comm, ← le_mul_inv_iff₀ h0, one_mul]
  rw [blockLat, mem_matLat_diagLat]
  simp only [h1]
  constructor
  · intro h
    exact ⟨fun i j hj => by simpa only [blockUnits, if_pos hj] using h i j,
      fun i j hj => by simpa [blockUnits, hj, Valuation.mem_integer_iff] using h i j⟩
  · rintro ⟨h, h'⟩ i j
    by_cases hj : j ∈ P
    · simpa only [blockUnits, if_pos hj] using h i j hj
    · simpa [blockUnits, hj, Valuation.mem_integer_iff] using h' i j hj

theorem mem_matLat_smul_blockLat {ϖ : kˣ} {e : ℕ} {P : Finset D} {X : Matrix A D k} :
    X ∈ matLat A (ϖ ^ e • blockLat ϖ e P) ↔
      (∀ i, ∀ j ∈ P, X i j ∈ 𝒪[k]) ∧ ∀ i, ∀ j ∉ P, valuation k (X i j) ≤ valuation k ((ϖ ^ e : kˣ) : k) := by
  rw [blockLat, smul_diagLat, mem_matLat_diagLat]
  constructor
  · intro h
    exact ⟨fun i j hj => by simpa [blockUnits, hj, Valuation.mem_integer_iff] using h i j,
      fun i j hj => by simpa only [blockUnits, if_neg hj, mul_one] using h i j⟩
  · rintro ⟨h, h'⟩ i j
    by_cases hj : j ∈ P
    · simpa [blockUnits, hj, Valuation.mem_integer_iff] using h i j hj
    · simpa only [blockUnits, if_neg hj, mul_one] using h' i j hj

variable [Fintype A] [DecidableEq A]

theorem hasDepth_fourierSum {ψ : AddChar k Circle} {ϖ : kˣ} (hϖ : IsUnif ϖ) (hψ : HasConductor ψ 1) (e : ℕ)
    (P : Finset D) {Φ : Matrix A D k → ℂ} (hΦ : IsNatDatum ϖ e Φ) :
    HasDepth ϖ e (blockLat ϖ e P) (fourierSum ψ ϖ e P Φ) := by
  classical
  have triv : ∀ y ∈ 𝒪[k], ψ y = 1 := fun y hy => (hψ 1).2 le_rfl y (by simpa using (show valuation k y ≤ 1 from hy))
  have hc : ((ϖ ^ e : kˣ) : k) ∈ 𝒪[k] := by
    rw [Units.val_pow_eq_pow_val]; exact pow_mem hϖ.mem e
  refine ⟨fun Y hY => ?_, fun Y Z hZ => ?_⟩
  · rw [fourierSum_apply]
    split_ifs with h
    · rw [Finset.sum_eq_zero, mul_zero]
      intro T _
      rw [hΦ.1, zero_mul]
      intro H
      refine hY (mem_matLat_blockLat.2 ⟨h, fun i j hj => ?_⟩)
      simpa [setCols, hj] using mem_matLat_stdLat.1 H i j
    · rfl
  · obtain ⟨h1, h2⟩ := mem_matLat_smul_blockLat.1 hZ
    rw [fourierSum_apply, fourierSum_apply]
    refine if_congr (forall_congr' fun i => forall₂_congr fun j hj => ?_) ?_ rfl
    · rw [Matrix.add_apply, mul_add, add_mem_cancel_right (mul_mem hc (h1 i j hj))]
    · congr 1
      refine Finset.sum_congr rfl fun T _ => ?_
      rw [setCols_add, pairCols_add, hΦ.2, AddChar.map_add_eq_mul, triv (pairCols P Z _), mul_one]
      · exact Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ => mul_mem (liftRes_mem T i j) (h1 i j j.2)
      · refine mem_matLat_smul_stdLat.2 fun i j => ?_
        by_cases hj : j ∈ P
        · simp [setCols, hj]
        · simpa only [setCols, of_apply, dif_neg hj] using h2 i j hj

theorem isNatDatum_invFourierSum {ψ : AddChar k Circle} {ϖ : kˣ} (hϖ : IsUnif ϖ) (hψ : HasConductor ψ 1) (e : ℕ)
    (P : Finset D) {Ψ : Matrix A D k → ℂ} (hΨ : HasDepth ϖ e (blockLat ϖ e P) Ψ) :
    IsNatDatum ϖ e (invFourierSum ψ ϖ e P Ψ) := by
  classical
  have triv : ∀ y ∈ 𝒪[k], ψ y = 1 := fun y hy => (hψ 1).2 le_rfl y (by simpa using (show valuation k y ≤ 1 from hy))
  have hc : ((ϖ ^ e : kˣ) : k) ∈ 𝒪[k] := by
    rw [Units.val_pow_eq_pow_val]; exact pow_mem hϖ.mem e
  have h0 : 0 < valuation k ((ϖ ^ e : kˣ) : k) := zero_lt_iff.2 (by simp)
  refine ⟨fun Y hY => ?_, fun Y Z hZ => ?_⟩
  · rw [invFourierSum_apply]
    split_ifs with h
    · refine Finset.sum_eq_zero fun S _ => ?_
      rw [hΨ.1, zero_mul]
      intro H
      refine hY (mem_matLat_stdLat.2 fun i j => ?_)
      by_cases hj : j ∈ P
      · exact h i j hj
      · simpa only [setCols, of_apply, dif_neg hj] using (mem_matLat_blockLat.1 H).2 i j hj
    · rfl
  · have h1 := mem_matLat_smul_stdLat.1 hZ
    rw [invFourierSum_apply, invFourierSum_apply]
    refine if_congr (forall_congr' fun i => forall₂_congr fun j _ => ?_) ?_ rfl
    · rw [Matrix.add_apply, add_mem_cancel_right (show Z i j ∈ 𝒪[k] from (Valuation.mem_integer_iff _ _).2
        ((h1 i j).trans ((Valuation.mem_integer_iff _ _).1 hc)))]
    · refine Finset.sum_congr rfl fun S _ => ?_
      rw [setCols_add, pairCols_add, hΨ.2, neg_add, AddChar.map_add_eq_mul, triv (-pairCols P Z _), mul_one]
      · refine neg_mem (Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ => ?_)
        have h2 : (((ϖ ^ e)⁻¹ : kˣ) : k) * Z i j ∈ 𝒪[k] := by
          rw [Valuation.mem_integer_iff, map_mul, Units.val_inv_eq_inv_val, map_inv₀, inv_mul_le_iff₀ h0, mul_one]
          exact h1 i j
        convert mul_mem (liftRes_mem S i j) h2 using 1
        simp only [Matrix.smul_apply, Units.smul_def, smul_eq_mul]
        ring
      · refine mem_matLat_smul_blockLat.2 ⟨fun i j hj => ?_, fun i j hj => ?_⟩
        · simp [setCols, hj]
        · simpa only [setCols, of_apply, dif_neg hj] using h1 i j

end GlobalTheory.SplitFlip.FourierDepth

theorem GlobalTheory.SplitFlip.FourierDepth.fourier_exchange (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]
    (ψ : AddChar k Circle) (ϖ : kˣ) (e : ℕ) (P : Finset D) (hϖ : IsUnif ϖ) (hψ : HasConductor ψ 1) :
    (∀ Φ : Matrix A D k → ℂ, IsNatDatum ϖ e Φ → HasDepth ϖ e (blockLat ϖ e P) (fourierSum ψ ϖ e P Φ)) ∧
      ∀ Ψ : Matrix A D k → ℂ, HasDepth ϖ e (blockLat ϖ e P) Ψ → IsNatDatum ϖ e (invFourierSum ψ ϖ e P Ψ) :=
  ⟨fun _ h => hasDepth_fourierSum hϖ hψ e P h, fun _ h => isNatDatum_invFourierSum hϖ hψ e P h⟩
