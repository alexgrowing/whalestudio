import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AtVecMulVecRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianSetAdditiveSubgroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviMapPreservesRationalPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianDeterminantNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrAEMixedNondeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfTraceOrth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumThreeComm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HTensEqTrace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HTensVmvLeft
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ArchSch GlobalTheory.ArchSchB

noncomputable section

namespace GlobalTheory.LeviPairing

section Gen

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A)

theorem hTens_transpose {α β : Type} [Fintype α] [Fintype β] (JA : Matrix α α A) (JB : Matrix β β A)
    (x y : Matrix α β A) : GlobalTheory.WeilM.hTens c JA JB x y = GlobalTheory.WeilM.hTens c JB JA xᵀ yᵀ := by
  unfold GlobalTheory.WeilM.hTens
  simp only [Matrix.transpose_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring

theorem map_mul_mul_transpose {α β α₁ β₁ : Type} [Fintype α₁] [Fintype β₁] (P : Matrix α α₁ A)
    (z : Matrix α₁ β₁ A) (Q : Matrix β β₁ A) :
    (P * z * Qᵀ).map c = P.map c * z.map c * (Q.map c)ᵀ := by
  ext i j
  simp [Matrix.mul_apply, map_sum, map_mul]

theorem hTens_vmv_left_zero {α β α₁ β₁ : Type} [Fintype α] [Fintype β] [Fintype α₁] [Fintype β₁]
    (JA : Matrix α α A) (JB : Matrix β β A) (P : Matrix α α₁ A) (Q : Matrix β β₁ A)
    (u : α → A) (a : β → A) (hu : u ᵥ* (JA * P.map c) = 0) (z : Matrix α₁ β₁ A) :
    GlobalTheory.WeilM.hTens c JA JB (Matrix.vecMulVec u a) (P * z * Qᵀ) = 0 := by
  rw [GlobalTheory.SympRestrict.hTens_eq_trace', map_mul_mul_transpose]
  have ht : (Matrix.vecMulVec u a)ᵀ = Matrix.vecMulVec a u := by
    ext i j; simp [Matrix.vecMulVec_apply, mul_comm]
  have key : (Matrix.vecMulVec u a)ᵀ * JA * (P.map c * z.map c * (Q.map c)ᵀ) * JBᵀ = 0 := by
    calc (Matrix.vecMulVec u a)ᵀ * JA * (P.map c * z.map c * (Q.map c)ᵀ) * JBᵀ
        = Matrix.vecMulVec a u * (JA * P.map c) * (z.map c * (Q.map c)ᵀ * JBᵀ) := by
          rw [ht]; simp only [Matrix.mul_assoc]
      _ = 0 := by
          have h0 : Matrix.vecMulVec a (0 : α₁ → A) = 0 := by ext; simp [Matrix.vecMulVec_apply]
          rw [Matrix.vecMulVec_mul, hu, h0, Matrix.zero_mul]
  rw [key, Matrix.trace_zero]

theorem hTens_vmv_right_zero {α β α₁ β₁ : Type} [Fintype α] [Fintype β] [Fintype α₁] [Fintype β₁]
    (JA : Matrix α α A) (JB : Matrix β β A) (P : Matrix α α₁ A) (Q : Matrix β β₁ A)
    (a : α → A) (w : β → A) (hw : w ᵥ* (JB * Q.map c) = 0) (z : Matrix α₁ β₁ A) :
    GlobalTheory.WeilM.hTens c JA JB (Matrix.vecMulVec a w) (P * z * Qᵀ) = 0 := by
  have ht : (Matrix.vecMulVec a w)ᵀ = Matrix.vecMulVec w a := by
    ext i j; simp [Matrix.vecMulVec_apply, mul_comm]
  have ht2 : (P * z * Qᵀ)ᵀ = Q * zᵀ * Pᵀ := by
    simp [Matrix.transpose_mul, Matrix.mul_assoc]
  rw [hTens_transpose, ht, ht2]
  exact hTens_vmv_left_zero c JB JA Q P w a hw zᵀ

theorem hTens_embed_both {α β α₁ β₁ : Type} [Fintype α] [Fintype β] [Fintype α₁] [Fintype β₁]
    (JA : Matrix α α A) (JB : Matrix β β A) (JA₁ : Matrix α₁ α₁ A) (JB₁ : Matrix β₁ β₁ A)
    (P : Matrix α α₁ A) (Q : Matrix β β₁ A) (hP : Pᵀ * JA * P.map c = JA₁) (hQ : Qᵀ * JB * Q.map c = JB₁)
    (z z' : Matrix α₁ β₁ A) :
    GlobalTheory.WeilM.hTens c JA JB (P * z * Qᵀ) (P * z' * Qᵀ) = GlobalTheory.WeilM.hTens c JA₁ JB₁ z z' := by
  rw [GlobalTheory.SympRestrict.hTens_embed c JA JB JB₁ Q hQ, hTens_transpose c JA JB₁, Matrix.transpose_mul,
    Matrix.transpose_mul, GlobalTheory.SympRestrict.hTens_embed c JB₁ JA JA₁ P hP, hTens_transpose c JA₁ JB₁]

end Gen

theorem form_swap_of_herm {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {d : ℕ}
    (J : Matrix (Fin d) (Fin d) E) (hσ : ∀ x, σ (σ x) = x) (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin d → E) :
    form σ J y x = σ (form σ J x y) := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, hJ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem form_swap_of_skewHerm {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {d : ℕ}
    (J : Matrix (Fin d) (Fin d) E) (hσ : ∀ x, σ (σ x) = x) (hJ : ∀ i j, σ (J j i) = -J i j) (x y : Fin d → E) :
    form σ J y x = -σ (form σ J x y) := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, hJ, Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem incV_vecMul_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n n₁ : ℕ} (J : Matrix (Fin n) (Fin n) E) (ι : Matrix (Fin n) (Fin n₁) E) (x : Fin n → E)
    (h : ∀ u, form σ J x (ι *ᵥ u) = 0) :
    incV F x ᵥ* (incM F J * (incM F ι).map (cA σ)) = 0 := by
  funext m
  have hE := congrArg (inclR (F := F) (AF F)) (h (Pi.single m 1))
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, map_zero, Pi.single_apply, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hE
  simp only [Matrix.vecMul, dotProduct, Matrix.mul_apply, incV, incM, Matrix.map_apply, Pi.zero_apply]
  rw [← hE]
  rfl

theorem pairing_eq : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (B : Base F E)
    {n d n₁ d₁ : ℕ} (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (H : Plane E n n₁) (H' : Plane E d d₁)
    (r s r' s' i₀ i₁ j₀ j₁ : ℕ),
    B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → H.IsAdapted σ B X X₁ i₀ i₁ → H'.IsAdapted σ B W W₁ j₀ j₁ →
    ∀ (α : Fin d → AE F E) (c₁ : Fin n₁ → AE F E) (Z z' : Matrix (Fin n₁) (Fin d₁) (AE F E)),
    symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)
      (Matrix.vecMulVec (incV F H.x) α + Matrix.vecMulVec (incM F H.ι *ᵥ c₁) (incV F H'.x) +
        incM F H.ι * Z * (incM F H'.ι)ᵀ) (incM F H.ι * z' * (incM F H'.ι)ᵀ) =
    symp (R := AF F) (cA σ) (-1) (incM F X₁.J) (incM F W₁.J) Z z' := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ H H' r s r' s' i₀ i₁ j₀ j₁ hB hX hW hH hH' α c₁ Z z'
  have hσ : ∀ x, σ (σ x) = x := fun x => by
    obtain ⟨-, -, -, h⟩ := hB.cm
    let τ : E →+* ℂ := Classical.choice (inferInstance : Nonempty (E →+* ℂ))
    apply τ.injective
    rw [h τ, h τ, star_star]
  have hgram : ∀ {k k₁ : ℕ} (J : Matrix (Fin k) (Fin k) E) (J₁ : Matrix (Fin k₁) (Fin k₁) E)
      (ι : Matrix (Fin k) (Fin k₁) E), ιᵀ * J * ι.map σ = J₁ →
      (incM F ι)ᵀ * incM F J * (incM F ι).map (cA σ) = incM F J₁ := by
    intro k k₁ J J₁ ι h
    have hι : (incM F ι).map (cA σ) = incM F (ι.map σ) := by
      ext i j
      simp [incM, cA, inclR]
    rw [hι, ← h]
    simp only [incM, Matrix.map_mul, Matrix.transpose_map]
  have hx : incV F H.x ᵥ* (incM F X.J * (incM F H.ι).map (cA σ)) = 0 :=
    incV_vecMul_zero X.J H.ι H.x fun u => by
      rw [form_swap_of_herm X.J hσ hX.herm, (hH.orth u).1, map_zero]
  have hw : incV F H'.x ᵥ* (incM F W.J * (incM F H'.ι).map (cA σ)) = 0 :=
    incV_vecMul_zero W.J H'.ι H'.x fun u => by
      rw [form_swap_of_skewHerm W.J hσ hW.skew, (hH'.orth u).1, map_zero, neg_zero]
  unfold symp
  rw [GlobalTheory.ArchSchB.TensForm.hTens_add_left, GlobalTheory.ArchSchB.TensForm.hTens_add_left,
    hTens_vmv_left_zero _ _ _ _ _ _ _ hx, hTens_vmv_right_zero _ _ _ _ _ _ _ hw,
    hTens_embed_both _ _ _ _ _ _ _ (hgram _ _ _ hH.gram) (hgram _ _ _ hH'.gram), zero_add, zero_add]

end GlobalTheory.LeviPairing
