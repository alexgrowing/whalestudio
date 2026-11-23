import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksMem
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

namespace GlobalTheory.InertDbl

theorem diag_mulVec_mem_latAt {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {d : ℕ} (W : Spc F E d) (v : Pl F) (M : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E))
    (t : Matrix (Fin d) (Fin d) (AE F E)) (h : M * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) = (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) * t)
    (hM : ∀ z ∈ latAtD W v, M *ᵥ z ∈ latAtD W v) (z : Fin d → AE F E) (hz : z ∈ GlobalTheory.InertSph.latAt W v) :
    t *ᵥ z ∈ GlobalTheory.InertSph.latAt W v := by
  have key : ∀ y : Fin d → AE F E,
      (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) *ᵥ y = Sum.elim y y := by
    intro y
    simp [diagCols, Matrix.fromRows_mulVec]
  have h1 : (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) *ᵥ z ∈ latAtD W v := by
    rw [key]; exact ⟨hz, hz⟩
  have h2 := hM _ h1
  rw [Matrix.mulVec_mulVec, h, ← Matrix.mulVec_mulVec, key] at h2
  exact h2.1

theorem parD_diag_action :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl F),
    ∀ p ∈ GlobalTheory.InertDbl.ParD σ W v, ∀ t : GL (Fin d) (AE F E),
      GlobalTheory.InertDbl.matD p * diagCols (Fin d) = diagCols (Fin d) * (t : Matrix (Fin d) (Fin d) (AE F E)) →
      At (evFin F v) ((t : Matrix (Fin d) (Fin d) (AE F E)) - 1) ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt W v, (t : Matrix (Fin d) (Fin d) (AE F E)) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v ∧
        ((t⁻¹ : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E)) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v := by
  intro F E _ _ _ _ _ σ d W v p hp t h'
  have h : matD p * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) =
      (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) * (t : Matrix (Fin d) (Fin d) (AE F E)) := h'
  obtain ⟨⟨hAt, hK⟩, -⟩ := hp
  have hinv : matD p⁻¹ * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) =
      (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) * ((t⁻¹ : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E)) := by
    have h1 : matD p⁻¹ * matD p = 1 := p.1.inv_mul
    have h2 : (t : Matrix (Fin d) (Fin d) (AE F E)) *
        ((t⁻¹ : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E)) = 1 := t.mul_inv
    calc matD p⁻¹ * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E))
        = matD p⁻¹ * ((diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) * ((t : Matrix (Fin d) (Fin d) (AE F E)) *
            ((t⁻¹ : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E)))) := by rw [h2, Matrix.mul_one]
      _ = _ := by
        rw [← Matrix.mul_assoc (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)), ← h, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  refine ⟨?_, fun z hz => ⟨diag_mulVec_mem_latAt W v _ _ h (fun y hy => (hK y hy).1) z hz,
    diag_mulVec_mem_latAt W v _ _ hinv (fun y hy => (hK y hy).2) z hz⟩⟩
  intro u hu
  have h0 := hAt u hu
  have h3 : (matD p - 1) * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) = (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) * ((t : Matrix (Fin d) (Fin d) (AE F E)) - 1) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, h, Matrix.one_mul, Matrix.mul_one]
  have h4 : (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) *
      (u • ((t : Matrix (Fin d) (Fin d) (AE F E)) - 1)) = 0 := by
    rw [Matrix.mul_smul, ← h3, ← Matrix.smul_mul, h0, Matrix.zero_mul]
  ext i j
  have h5 := congrFun (congrFun h4 (Sum.inl i)) j
  rw [diagCols, Matrix.fromRows_mul, Matrix.one_mul] at h5
  exact h5

end GlobalTheory.InertDbl
