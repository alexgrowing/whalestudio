import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ThK.LevNorm

theorem conj_unip_mem : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n₁ : ℕ) (X : Spc F E (n₁ + 2)) (X₁ : Spc F E n₁) (H : Plane E (n₁ + 2) n₁),
    ∀ (t : (AE F E)ˣ) (a : UA σ X.J), IsLevi (W₁ := X₁) H t 1 a → ∀ n ∈ unip σ X H, a * n * a⁻¹ ∈ unip σ X H := by
  intro F E _ _ _ _ _ σ n₁ X X₁ H t a hL n hn
  obtain ⟨hx, -, hι⟩ := hL
  have hmul : ∀ g h : UA σ X.J, mat (g * h) = mat g * mat h := fun _ _ => rfl
  have hinv : mat a⁻¹ * mat a = 1 := by
    show ((a⁻¹ : UA σ X.J) : GL (Fin (n₁ + 2)) (AE F E)).val * (a : GL (Fin (n₁ + 2)) (AE F E)).val = 1
    rw [Subgroup.coe_inv, Units.inv_mul]
  have hone : mat (1 : UA σ X₁.J) = 1 := rfl
  rw [hone, Matrix.mul_one] at hι

  have hιinv : mat a⁻¹ * incM F H.ι = incM F H.ι := by
    calc mat a⁻¹ * incM F H.ι = mat a⁻¹ * (mat a * incM F H.ι) := by rw [hι]
      _ = incM F H.ι := by rw [← Matrix.mul_assoc, hinv, Matrix.one_mul]
  have hxinv : mat a⁻¹ *ᵥ incV F H.x = (t⁻¹ : (AE F E)ˣ).1 • incV F H.x := by
    calc mat a⁻¹ *ᵥ incV F H.x = mat a⁻¹ *ᵥ ((t⁻¹ : (AE F E)ˣ).1 • (t.1 • incV F H.x)) := by
          rw [smul_smul, Units.inv_mul, one_smul]
      _ = (t⁻¹ : (AE F E)ˣ).1 • (mat a⁻¹ *ᵥ (mat a *ᵥ incV F H.x)) := by rw [hx, Matrix.mulVec_smul]
      _ = (t⁻¹ : (AE F E)ˣ).1 • incV F H.x := by rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  let S : Set (UA σ X.J) := {u | mat u *ᵥ incV F H.x = incV F H.x ∧
    ∀ z, ∃ c : AE F E, mat u *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z + c • incV F H.x}
  have hS : ∀ u ∈ S, a * u * a⁻¹ ∈ S := by
    rintro u ⟨hu1, hu2⟩
    refine ⟨?_, fun z => ?_⟩
    · rw [hmul, hmul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hxinv, Matrix.mulVec_smul, hu1,
        Matrix.mulVec_smul, hx, smul_smul, Units.inv_mul, one_smul]
    · obtain ⟨c, hc⟩ := hu2 z
      refine ⟨c * t.1, ?_⟩
      have h1 : mat a⁻¹ *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z := by rw [Matrix.mulVec_mulVec, hιinv]
      have h2 : mat a *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z := by rw [Matrix.mulVec_mulVec, hι]
      rw [hmul, hmul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h1, hc, Matrix.mulVec_add, h2,
        Matrix.mulVec_smul, hx, smul_smul]
  have hle : unip σ X H ≤ (unip σ X H).comap (MulAut.conj a).toMonoidHom := by
    rw [unip, Subgroup.closure_le]
    intro u hu
    show (MulAut.conj a) u ∈ Subgroup.closure S
    rw [MulAut.conj_apply]
    exact Subgroup.subset_closure (hS u hu)
  have := hle hn
  simpa [MulAut.conj_apply] using this

end GlobalTheory.ThK.LevNorm
