import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockOfMatrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

namespace GlobalTheory

theorem integralBlocks_leftInverse_isUnit_det : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {d : ℕ} (v : Pl F) (π : AE F E →+* Fv F v) (b : GL (Fin d) (Fv F v))
  (g h : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)), h * g = 1 →
  (∀ i j, (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * ((g).toBlocks₁₁).map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F) →
  (∀ i j, (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * ((g).toBlocks₁₂).map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F) →
  (∀ i j, (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * ((g).toBlocks₂₁).map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F) →
  (∀ i j, (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * ((g).toBlocks₂₂).map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F) →
  (∀ i j, (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * ((h).toBlocks₁₁).map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F) →
  (∀ i j, (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * ((h).toBlocks₁₂).map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F) →
  (∀ i j, (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * ((h).toBlocks₂₁).map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F) →
  (∀ i j, (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * ((h).toBlocks₂₂).map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F) →
  ∃ G : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (v.adicCompletionIntegers F), G.map (fun x => (x : Fv F v)) = Matrix.fromBlocks (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (g).toBlocks₁₁.map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (g).toBlocks₁₂.map π * (b : Matrix (Fin d) (Fin d) (Fv F v)))
      (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (g).toBlocks₂₁.map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (g).toBlocks₂₂.map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) ∧ IsUnit G.det := by
  intro F E _ _ _ _ _ d v π b g h hhg g11 g12 g21 g22 h11 h12 h21 h22
  classical
  set Bi : Matrix (Fin d) (Fin d) (Fv F v) := ((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) with hBi
  set Bm : Matrix (Fin d) (Fin d) (Fv F v) := (b : Matrix (Fin d) (Fin d) (Fv F v)) with hBm
  have hbb : Bm * Bi = 1 := by
    simp only [hBi, hBm]
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hbb' : Bi * Bm = 1 := by
    simp only [hBi, hBm]
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have key : ∀ x : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E),
      Matrix.fromBlocks (Bi * x.toBlocks₁₁.map π * Bm) (Bi * x.toBlocks₁₂.map π * Bm)
        (Bi * x.toBlocks₂₁.map π * Bm) (Bi * x.toBlocks₂₂.map π * Bm)
      = Matrix.fromBlocks Bi 0 0 Bi * x.map π * Matrix.fromBlocks Bm 0 0 Bm := by
    intro x
    have hx : x.map π = Matrix.fromBlocks (x.toBlocks₁₁.map π) (x.toBlocks₁₂.map π)
        (x.toBlocks₂₁.map π) (x.toBlocks₂₂.map π) := by
      rw [← Matrix.fromBlocks_map, Matrix.fromBlocks_toBlocks]
    rw [hx, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp
  have hprod : (Matrix.fromBlocks Bi 0 0 Bi * h.map π * Matrix.fromBlocks Bm 0 0 Bm) *
      (Matrix.fromBlocks Bi 0 0 Bi * g.map π * Matrix.fromBlocks Bm 0 0 Bm) = 1 := by
    have hBB : Matrix.fromBlocks Bm 0 0 Bm * Matrix.fromBlocks Bi 0 0 Bi = (1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (Fv F v)) := by
      rw [Matrix.fromBlocks_multiply]; simp [hbb]
    have hBB' : Matrix.fromBlocks Bi 0 0 Bi * Matrix.fromBlocks Bm 0 0 Bm = (1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (Fv F v)) := by
      rw [Matrix.fromBlocks_multiply]; simp [hbb']
    have hhg' : h.map π * g.map π = 1 := by
      rw [← Matrix.map_mul, hhg, Matrix.map_one _ (map_zero π) (map_one π)]
    calc (Matrix.fromBlocks Bi 0 0 Bi * h.map π * Matrix.fromBlocks Bm 0 0 Bm) *
          (Matrix.fromBlocks Bi 0 0 Bi * g.map π * Matrix.fromBlocks Bm 0 0 Bm)
        = Matrix.fromBlocks Bi 0 0 Bi * h.map π * (Matrix.fromBlocks Bm 0 0 Bm *
          Matrix.fromBlocks Bi 0 0 Bi) * g.map π * Matrix.fromBlocks Bm 0 0 Bm := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [hBB, Matrix.mul_one, Matrix.mul_assoc (Matrix.fromBlocks Bi 0 0 Bi), hhg', Matrix.mul_one, hBB']

  let G : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (v.adicCompletionIntegers F) := fun i j =>
    match i, j with
    | Sum.inl i, Sum.inl j => ⟨_, g11 i j⟩
    | Sum.inl i, Sum.inr j => ⟨_, g12 i j⟩
    | Sum.inr i, Sum.inl j => ⟨_, g21 i j⟩
    | Sum.inr i, Sum.inr j => ⟨_, g22 i j⟩
  let H : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (v.adicCompletionIntegers F) := fun i j =>
    match i, j with
    | Sum.inl i, Sum.inl j => ⟨_, h11 i j⟩
    | Sum.inl i, Sum.inr j => ⟨_, h12 i j⟩
    | Sum.inr i, Sum.inl j => ⟨_, h21 i j⟩
    | Sum.inr i, Sum.inr j => ⟨_, h22 i j⟩
  have hG : G.map (fun x => (x : Fv F v)) = Matrix.fromBlocks (Bi * g.toBlocks₁₁.map π * Bm) (Bi * g.toBlocks₁₂.map π * Bm)
        (Bi * g.toBlocks₂₁.map π * Bm) (Bi * g.toBlocks₂₂.map π * Bm) := by
    ext i j; rcases i with i | i <;> rcases j with j | j <;> rfl
  have hH : H.map (fun x => (x : Fv F v)) = Matrix.fromBlocks (Bi * h.toBlocks₁₁.map π * Bm) (Bi * h.toBlocks₁₂.map π * Bm)
        (Bi * h.toBlocks₂₁.map π * Bm) (Bi * h.toBlocks₂₂.map π * Bm) := by
    ext i j; rcases i with i | i <;> rcases j with j | j <;> rfl
  refine ⟨G, hG, ?_⟩
  apply Matrix.isUnit_det_of_left_inverse (B := H)
  have hmap : (H * G).map (v.adicCompletionIntegers F).subtype = 1 := by
    rw [Matrix.map_mul]
    change H.map (fun x => (x : Fv F v)) * G.map (fun x => (x : Fv F v)) = 1
    rw [hG, hH, key, key, hprod]
  refine Matrix.ext fun i j => Subtype.coe_injective ?_
  have := congrFun (congrFun hmap i) j
  rw [Matrix.map_apply] at this
  change (v.adicCompletionIntegers F).subtype ((H * G) i j) = (v.adicCompletionIntegers F).subtype ((1 : Matrix _ _ _) i j)
  rw [this, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

end GlobalTheory
