import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentCoordinateAdditive
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.UnipDom
open GlobalTheory.Doubling (absE)

open GlobalTheory.ThK.UnipDom.Additive in

theorem GlobalTheory.ThK.UnipDom.coA_mul_of_isIsoPlane : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n n₁ : ℕ) (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁), IsCMExt F E σ → (∀ i j, σ (Y.J j i) = -Y.J i j) → IsIsoPlane σ B H Y Y₁ → ∀ u ∈ unip σ Y H, ∀ v ∈ unip σ Y H, coA σ Y.J H (u * v) = coA σ Y.J H u + coA σ Y.J H v := by
  intro F E _ _ _ _ _ σ B d d₁ W W₁ H' _ _ hA u hu v hv
  obtain ⟨-, -, -, hxy, horth, -⟩ := hA
  funext j
  set e : Fin d → AE F E := incM F H'.ι *ᵥ Pi.single j 1 with he
  have hval : ∀ c : AE F E, fA σ W.J (e + c • incV F H'.x) (incV F H'.y) = c := by
    intro c
    rw [fA_add_left, fA_smul_left, fA_incV, hxy, map_one, mul_one, he, single_eq_incV,
      incM_mulVec_incV, fA_incV, (horth _).2, map_zero, zero_add]
  obtain ⟨a, ha⟩ := (unip_spec hu).2 (Pi.single j 1)
  obtain ⟨b, hb⟩ := (unip_spec hv).2 (Pi.single j 1)
  have hux := (unip_spec hu).1
  have huv : mat (u * v) *ᵥ e = e + (a + b) • incV F H'.x := by
    rw [mat_mul', ← Matrix.mulVec_mulVec, he, hb, Matrix.mulVec_add, Matrix.mulVec_smul, hux, ha, add_smul, add_assoc]
  simp only [Pi.add_apply, coA]
  rw [← he, huv, hval, ha, ← he, hval, hb, ← he, hval]
