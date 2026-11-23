import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetAdaptedBasisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedBasisGramEqStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.QhtUnip

namespace GlobalTheory.QhtUnip

theorem gram_basQ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ e, σ (σ e) = e) (B : Base F E) {m : ℕ} (W : Spc F E (m + 2)) (r s : ℕ) (hW : W.IsSkew σ B r s)
    (W₁ : Spc F E m) (H : Plane E (m + 2) m) (i₀ i₁ : ℕ) (hA : H.IsAdapted σ B W W₁ i₀ i₁) :
    (basQ H)ᵀ * W.J * (basQ H).map σ = (gI W₁.J).submatrix (ixE m) (ixE m) := by
  ext i j
  have h := GlobalTheory.T.adapted_basis_gram_eq F E σ hσ B W r s hW W₁ H i₀ i₁ hA (ixE m i) (ixE m j)
  rw [Matrix.submatrix_apply, ← h]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, form, dotProduct, Matrix.mulVec,
    basQ, Matrix.submatrix_apply, id, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem cA_inclR {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (e : E) :
    cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := by
  simp [cA, inclR]

theorem unit_crd : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), (∀ e, σ (σ e) = e) → ∀ (B : Base F E) {m : ℕ} (W : Spc F E (m + 2)) (r s : ℕ), W.IsSkew σ B r s →
    ∀ (W₁ : Spc F E m) (H : Plane E (m + 2) m) (i₀ i₁ : ℕ), H.IsAdapted σ B W W₁ i₀ i₁ → ∀ g : UA σ W.J, (crd H g)ᵀ * (gI W₁.J).map (inclR (F := F) (AF F)) * (crd H g).map (cA σ) =
      (gI W₁.J).map (inclR (F := F) (AF F)) := by
  intro F E _ _ _ _ _ σ hσ B m W r s hW W₁ H i₀ i₁ hA g
  set e := ixE m
  set P := incM F (basQ H) with hP
  have hdet : IsUnit P.det := by
    rw [hP, incM, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (GlobalTheory.T.isUnit_det_adapted_basis F E σ B W r s hW W₁ H i₀ i₁ hA).map _
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hdet
  have hPPt : (P⁻¹)ᵀ * Pᵀ = 1 := by rw [← Matrix.transpose_mul, hPP, Matrix.transpose_one]
  have hPPc : P.map (cA σ) * (P⁻¹).map (cA σ) = 1 := by
    rw [← Matrix.map_mul, hPP, Matrix.map_one _ (map_zero _) (map_one _)]
  have hG : Pᵀ * incM F W.J * P.map (cA σ) = ((gI W₁.J).submatrix e e).map (inclR (F := F) (AF F)) := by
    rw [← gram_basQ σ hσ B W r s hW W₁ H i₀ i₁ hA, hP]
    simp only [incM, Matrix.map_mul, Matrix.transpose_map, Matrix.map_map]
    have hc : (⇑(cA σ) ∘ ⇑(inclR (F := F) (AF F))) = ⇑(inclR (F := F) (AF F)) ∘ ⇑σ := funext (cA_inclR σ)
    rw [hc]
  have hg : (mat g)ᵀ * incM F W.J * (mat g).map (cA σ) = incM F W.J := g.2
  have hPPt' : ∀ X : Matrix (Fin (m + 2)) (Fin (m + 2)) (AE F E), (P⁻¹)ᵀ * (Pᵀ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hPPt, Matrix.one_mul]
  have hPPc' : ∀ X : Matrix (Fin (m + 2)) (Fin (m + 2)) (AE F E), P.map (cA σ) * ((P⁻¹).map (cA σ) * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hPPc, Matrix.one_mul]
  have hg' : ∀ X : Matrix (Fin (m + 2)) (Fin (m + 2)) (AE F E),
      (mat g)ᵀ * (incM F W.J * ((mat g).map (cA σ) * X)) = incM F W.J * X := fun X => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hg]
  have key : (P⁻¹ * mat g * P)ᵀ * (Pᵀ * incM F W.J * P.map (cA σ)) * (P⁻¹ * mat g * P).map (cA σ) =
      Pᵀ * incM F W.J * P.map (cA σ) := by
    simp only [Matrix.transpose_mul, Matrix.map_mul, Matrix.mul_assoc]
    rw [hPPt', hPPc', hg']
  rw [hG] at key
  have hgI : (gI W₁.J).map (inclR (F := F) (AF F)) =
      (((gI W₁.J).submatrix e e).map (inclR (F := F) (AF F))).submatrix e.symm e.symm := by
    ext i j; simp
  have hcrd : crd H g = (P⁻¹ * mat g * P).submatrix e.symm e.symm := rfl
  have hsub : ∀ A B C : Matrix (Fin (m + 2)) (Fin (m + 2)) (AE F E),
      (A.submatrix e.symm e.symm)ᵀ * B.submatrix e.symm e.symm * (C.submatrix e.symm e.symm).map (cA σ) =
        (Aᵀ * B * C.map (cA σ)).submatrix e.symm e.symm := by
    intro A B C
    rw [Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, ← Matrix.submatrix_map, Matrix.submatrix_mul_equiv]
  rw [hgI, hcrd, hsub, key]

end GlobalTheory.QhtUnip
