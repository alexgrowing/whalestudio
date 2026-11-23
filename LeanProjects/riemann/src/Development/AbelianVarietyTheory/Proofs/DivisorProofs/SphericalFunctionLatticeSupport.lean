import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot
open Formalism.L2.Host (aboveF)
open Formalism.UG (IsUnifV qV)

noncomputable section

namespace GlobalTheory.ThK.Bot

section IntMat

variable {F : Type} [Field F] [NumberField F] {v : Pl F} {n d : ℕ}

theorem intMat_mul {A : Matrix (Fin n) (Fin n) (Fv F v)} {M : Matrix (Fin n) (Fin d) (Fv F v)}
    (hA : ∀ i j, A i j ∈ v.adicCompletionIntegers F) (hM : ∀ i j, M i j ∈ v.adicCompletionIntegers F) :
    ∀ i j, (A * M) i j ∈ v.adicCompletionIntegers F := fun i j => by
  rw [Matrix.mul_apply]
  exact sum_mem fun k _ => mul_mem (hA i k) (hM k j)

theorem intMat_kgl_mul_iff {k : GL (Fin n) (Fv F v)} (hk : k ∈ KGL v n) (M : Matrix (Fin n) (Fin d) (Fv F v)) :
    (∀ i j, (k.1 * M) i j ∈ v.adicCompletionIntegers F) ↔ ∀ i j, M i j ∈ v.adicCompletionIntegers F := by
  obtain ⟨h1, h2⟩ := mem_GLint_iff.1 hk
  refine ⟨fun h => ?_, fun h => intMat_mul h1 h⟩
  have e : M = (k⁻¹).1 * (k.1 * M) := by
    rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  rw [e]
  exact intMat_mul h2 h

theorem diag_inv_mul_apply {ϖ : Fv F v} (hϖ : ϖ ≠ 0) (e : Fin n → ℤ) {T : GL (Fin n) (Fv F v)}
    (hT : T.1 = Matrix.diagonal (fun i => ϖ ^ e i)) (M : Matrix (Fin n) (Fin d) (Fv F v)) (i : Fin n) (j : Fin d) :
    ((T⁻¹).1 * M) i j = ϖ ^ (-e i) * M i j := by
  have h : T.1 * ((T⁻¹).1 * M) = M := by
    rw [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  have h' := congrFun (congrFun h i) j
  rw [hT, Matrix.diagonal_mul] at h'
  rw [← h', ← mul_assoc, ← zpow_add₀ hϖ, neg_add_cancel, zpow_zero, one_mul]

theorem zpow_mem_of_nonneg {ϖ : Fv F v} (hϖ : ϖ ∈ v.adicCompletionIntegers F) {m : ℤ} (hm : 0 ≤ m) :
    ϖ ^ m ∈ v.adicCompletionIntegers F := by
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hm
  rw [zpow_natCast]
  exact pow_mem hϖ k

theorem zpow_max_mem_iff {ϖ : Fv F v} (hϖ : ϖ ∈ v.adicCompletionIntegers F) (hϖ0 : ϖ ≠ 0) (e : ℤ) (z : Fv F v) :
    ϖ ^ (-max e 0) * z ∈ v.adicCompletionIntegers F ↔
      ϖ ^ (-e) * z ∈ v.adicCompletionIntegers F ∧ z ∈ v.adicCompletionIntegers F := by
  rcases le_total e 0 with he | he
  · rw [max_eq_right he, neg_zero, zpow_zero, one_mul]
    exact ⟨fun h => ⟨mul_mem (zpow_mem_of_nonneg hϖ (by omega)) h, h⟩, fun h => h.2⟩
  · rw [max_eq_left he]
    refine ⟨fun h => ⟨h, ?_⟩, fun h => h.1⟩
    have : z = ϖ ^ e * (ϖ ^ (-e) * z) := by
      rw [← mul_assoc, ← zpow_add₀ hϖ0, add_neg_cancel, zpow_zero, one_mul]
    rw [this]
    exact mul_mem (zpow_mem_of_nonneg hϖ he) h

end IntMat

theorem inter_kdiag_int_iff : ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) (n d : ℕ),
    ∀ (ϖ : (Fv F v)ˣ), IsUnifV F v ϖ.1 → ∀ (e : Fin n → ℤ) (T : GL (Fin n) (Fv F v)), T.1 = Matrix.diagonal (fun i => ϖ.1 ^ e i) → ∀ k₁ ∈ KGL v n, ∀ k₂ ∈ KGL v n,
    ∀ T' : GL (Fin n) (Fv F v), T'.1 = Matrix.diagonal (fun i => ϖ.1 ^ max (e i) 0) → ∀ Y : Matrix (Fin n) (Fin d) (Fv F v),
      (∀ i j, (((k₁ * T')⁻¹).1 * Y) i j ∈ v.adicCompletionIntegers F) ↔
        (∀ i j, (((k₁ * T * k₂)⁻¹).1 * Y) i j ∈ v.adicCompletionIntegers F) ∧ ∀ i j, Y i j ∈ v.adicCompletionIntegers F := by
  intro F _ _ v n d ϖ hu e T hT k₁ hk₁ k₂ hk₂ T' hT' Y
  have hϖ : ϖ.1 ∈ v.adicCompletionIntegers F := mem_Ov_of_isUnifV hu
  have hϖ0 : ϖ.1 ≠ 0 := ϖ.ne_zero
  have hk₁i : k₁⁻¹ ∈ KGL v n := inv_mem hk₁
  have hk₂i : k₂⁻¹ ∈ KGL v n := inv_mem hk₂
  set Z := (k₁⁻¹).1 * Y with hZ
  have eL : ((k₁ * T')⁻¹).1 * Y = (T'⁻¹).1 * Z := by
    rw [hZ, mul_inv_rev, Units.val_mul, Matrix.mul_assoc]
  have eR : ((k₁ * T * k₂)⁻¹).1 * Y = (k₂⁻¹).1 * ((T⁻¹).1 * Z) := by
    rw [hZ, mul_inv_rev, mul_inv_rev, Units.val_mul, Units.val_mul, Matrix.mul_assoc, Matrix.mul_assoc]
  have eY : (∀ i j, Y i j ∈ v.adicCompletionIntegers F) ↔ ∀ i j, Z i j ∈ v.adicCompletionIntegers F :=
    (intMat_kgl_mul_iff hk₁i Y).symm
  rw [eL, eR, intMat_kgl_mul_iff hk₂i, eY]
  have hT'' : T'.1 = Matrix.diagonal (fun i => ϖ.1 ^ (max (e i) 0)) := hT'
  simp only [diag_inv_mul_apply hϖ0 _ hT'', diag_inv_mul_apply hϖ0 _ hT]
  constructor
  · intro h
    exact ⟨fun i j => ((zpow_max_mem_iff hϖ hϖ0 (e i) (Z i j)).1 (h i j)).1,
      fun i j => ((zpow_max_mem_iff hϖ hϖ0 (e i) (Z i j)).1 (h i j)).2⟩
  · rintro ⟨h1, h2⟩ i j
    exact (zpow_max_mem_iff hϖ hϖ0 (e i) (Z i j)).2 ⟨h1 i j, h2 i j⟩

end GlobalTheory.ThK.Bot

end
