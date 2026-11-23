import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockOfMatrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

namespace GlobalTheory.Twist

theorem halfBlockSum_inv_conj_integral : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {d : ℕ} (v : Pl F) (π : AE F E →+* Fv F v) (b : GL (Fin d) (Fv F v)),
  (∀ a : AF F, π (algebraMap (AF F) (AE F E) a) = evFin F v a) →
  ∀ (g : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) (G : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (v.adicCompletionIntegers F)),
  G.map (fun x => (x : Fv F v)) = Matrix.fromBlocks (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (g).toBlocks₁₁.map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (g).toBlocks₁₂.map π * (b : Matrix (Fin d) (Fin d) (Fv F v)))
      (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (g).toBlocks₂₁.map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (g).toBlocks₂₂.map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) →
  ∀ X : Matrix (Fin d) (Fin d) (v.adicCompletionIntegers F),
  IsUnit (G.toBlocks₁₁ + G.toBlocks₁₂ + G.toBlocks₂₁ + G.toBlocks₂₂ +
    X * (G.toBlocks₁₁ + G.toBlocks₁₂ - G.toBlocks₂₁ - G.toBlocks₂₂)).det →
  ∀ Y : Matrix (Fin d) (Fin d) (AE F E), Y.map π = (b : Matrix (Fin d) (Fin d) (Fv F v)) * X.map (fun x => (x : Fv F v)) * ((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) →
  ∃ N : Matrix (Fin d) (Fin d) (Fv F v), N * (⅟(2 : AF F) • ((g).toBlocks₁₁ + (g).toBlocks₁₂ + (g).toBlocks₂₁ + (g).toBlocks₂₂) +
      Y * (⅟(2 : AF F) • ((g).toBlocks₁₁ + (g).toBlocks₁₂ - (g).toBlocks₂₁ - (g).toBlocks₂₂))).map π = 1 ∧ (∀ i j, (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * N * (b : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F) := by
  intro F E _ _ _ _ _ d v π b hπ g G hG X hdet Y hY
  set B : Matrix (Fin d) (Fin d) (Fv F v) := (b : Matrix (Fin d) (Fin d) (Fv F v)) with hB
  set Bi : Matrix (Fin d) (Fin d) (Fv F v) := ((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) with hBi
  have hBBi : B * Bi = 1 := Units.mul_inv b
  have hBiB : Bi * B = 1 := Units.inv_mul b
  let φ : v.adicCompletionIntegers F →+* Fv F v := (v.adicCompletionIntegers F).subtype
  have conj : ∀ M : Matrix (Fin d) (Fin d) (Fv F v), B * (Bi * M * B) * Bi = M := by
    intro M
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hBBi, Matrix.one_mul, Matrix.mul_assoc, hBBi,
      Matrix.mul_one]
  have hGφ : G.map (fun x => (x : Fv F v)) = G.map φ := rfl
  rw [hGφ] at hG
  have h11 : g.toBlocks₁₁.map π = B * G.toBlocks₁₁.map φ * Bi := by
    have := congrArg Matrix.toBlocks₁₁ hG
    rw [Matrix.toBlocks_fromBlocks₁₁] at this
    have e : (G.map φ).toBlocks₁₁ = G.toBlocks₁₁.map φ := rfl
    rw [e] at this; rw [this, conj]
  have h12 : g.toBlocks₁₂.map π = B * G.toBlocks₁₂.map φ * Bi := by
    have := congrArg Matrix.toBlocks₁₂ hG
    rw [Matrix.toBlocks_fromBlocks₁₂] at this
    have e : (G.map φ).toBlocks₁₂ = G.toBlocks₁₂.map φ := rfl
    rw [e] at this; rw [this, conj]
  have h21 : g.toBlocks₂₁.map π = B * G.toBlocks₂₁.map φ * Bi := by
    have := congrArg Matrix.toBlocks₂₁ hG
    rw [Matrix.toBlocks_fromBlocks₂₁] at this
    have e : (G.map φ).toBlocks₂₁ = G.toBlocks₂₁.map φ := rfl
    rw [e] at this; rw [this, conj]
  have h22 : g.toBlocks₂₂.map π = B * G.toBlocks₂₂.map φ * Bi := by
    have := congrArg Matrix.toBlocks₂₂ hG
    rw [Matrix.toBlocks_fromBlocks₂₂] at this
    have e : (G.map φ).toBlocks₂₂ = G.toBlocks₂₂.map φ := rfl
    rw [e] at this; rw [this, conj]
  have hYφ : Y.map π = B * X.map φ * Bi := hY
  set c : Fv F v := π (algebraMap (AF F) (AE F E) ⅟(2 : AF F)) with hc
  have hc2 : (2 : Fv F v) * c = 1 := by
    rw [hc, hπ, ← map_ofNat (evFin F v) 2, ← map_mul, mul_invOf_self, map_one]
  have hsm : ∀ M : Matrix (Fin d) (Fin d) (AE F E), (⅟(2 : AF F) • M).map π = c • M.map π := by
    intro M; ext i j
    rw [Matrix.map_apply, Matrix.smul_apply, Algebra.smul_def, map_mul, Matrix.smul_apply, Matrix.map_apply, hc, smul_eq_mul]
  have aπ : ∀ M N : Matrix (Fin d) (Fin d) (AE F E), (M + N).map π = M.map π + N.map π :=
    fun M N => Matrix.map_add π (map_add π) M N
  have sπ : ∀ M N : Matrix (Fin d) (Fin d) (AE F E), (M - N).map π = M.map π - N.map π :=
    fun M N => Matrix.map_sub π (map_sub π) M N
  have aφ : ∀ M N : Matrix (Fin d) (Fin d) (v.adicCompletionIntegers F), (M + N).map φ = M.map φ + N.map φ :=
    fun M N => Matrix.map_add φ (map_add φ) M N
  have sφ : ∀ M N : Matrix (Fin d) (Fin d) (v.adicCompletionIntegers F), (M - N).map φ = M.map φ - N.map φ :=
    fun M N => Matrix.map_sub φ (map_sub φ) M N
  set s := G.toBlocks₁₁ + G.toBlocks₁₂ + G.toBlocks₂₁ + G.toBlocks₂₂ with hs
  set t := G.toBlocks₁₁ + G.toBlocks₁₂ - G.toBlocks₂₁ - G.toBlocks₂₂ with ht
  set P := s + X * t with hP
  have hSπ : (g.toBlocks₁₁ + g.toBlocks₁₂ + g.toBlocks₂₁ + g.toBlocks₂₂).map π = B * s.map φ * Bi := by
    simp only [aπ, aφ, h11, h12, h21, h22, hs, Matrix.mul_add, Matrix.add_mul]
  have hTπ : (g.toBlocks₁₁ + g.toBlocks₁₂ - g.toBlocks₂₁ - g.toBlocks₂₂).map π = B * t.map φ * Bi := by
    simp only [aπ, sπ, aφ, sφ, h11, h12, h21, h22, ht, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_sub, Matrix.sub_mul]
  have hK : (⅟(2 : AF F) • (g.toBlocks₁₁ + g.toBlocks₁₂ + g.toBlocks₂₁ + g.toBlocks₂₂) +
      Y * (⅟(2 : AF F) • (g.toBlocks₁₁ + g.toBlocks₁₂ - g.toBlocks₂₁ - g.toBlocks₂₂))).map π
      = c • (B * P.map φ * Bi) := by
    rw [aπ, Matrix.map_mul, hsm, hsm, hSπ, hTπ, hYφ, hP, aφ s (X * t), Matrix.map_mul (f := φ) (M := t) (L := X)]
    rw [Matrix.mul_smul, ← smul_add]
    congr 1
    have : B * X.map φ * Bi * (B * t.map φ * Bi) = B * (X.map φ * t.map φ) * Bi := by
      calc B * X.map φ * Bi * (B * t.map φ * Bi) = B * X.map φ * (Bi * B) * t.map φ * Bi := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hBiB, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    rw [this, ← Matrix.add_mul, ← Matrix.mul_add]
  refine ⟨(2 : Fv F v) • (B * (P⁻¹).map φ * Bi), ?_, ?_⟩
  · rw [hK, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hc2, one_smul]
    have hPinv : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet
    calc B * (P⁻¹).map φ * Bi * (B * P.map φ * Bi) = B * ((P⁻¹).map φ * (Bi * B) * P.map φ) * Bi := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [hBiB, Matrix.mul_one, ← Matrix.map_mul, hPinv, Matrix.map_one _ (map_zero φ) (map_one φ),
            Matrix.mul_one, hBBi]
  · intro i j
    have : Bi * ((2 : Fv F v) • (B * (P⁻¹).map φ * Bi)) * B = (2 : Fv F v) • (P⁻¹).map φ := by
      rw [Matrix.mul_smul, Matrix.smul_mul]
      congr 1
      calc Bi * (B * (P⁻¹).map φ * Bi) * B = (Bi * B) * (P⁻¹).map φ * (Bi * B) := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hBiB, Matrix.one_mul, Matrix.mul_one]
    rw [this, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    have e : (2 : Fv F v) * φ (P⁻¹ i j) = φ (2 * P⁻¹ i j) := by rw [map_mul, map_ofNat]
    rw [e]
    exact (2 * P⁻¹ i j).2

end GlobalTheory.Twist
