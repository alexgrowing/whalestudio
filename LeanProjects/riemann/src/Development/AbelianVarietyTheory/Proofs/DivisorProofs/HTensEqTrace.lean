import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPApply
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ArchSch

noncomputable section

namespace GlobalTheory.SympRestrict

theorem hTens_eq_trace' {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) {α β : Type} [Fintype α]
    [Fintype β] (JA : Matrix α α A) (JB : Matrix β β A) (x y : Matrix α β A) :
    GlobalTheory.WeilM.hTens c JA JB x y = (xᵀ * JA * y.map c * JBᵀ).trace := by
  simp only [GlobalTheory.WeilM.hTens, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => by ring

theorem hTens_embed {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) {α β β₁ : Type} [Fintype α]
    [Fintype β] [Fintype β₁] (JA : Matrix α α A) (JB : Matrix β β A) (JB₁ : Matrix β₁ β₁ A) (ι : Matrix β β₁ A)
    (h : ιᵀ * JB * ι.map c = JB₁) (z z' : Matrix α β₁ A) :
    GlobalTheory.WeilM.hTens c JA JB (z * ιᵀ) (z' * ιᵀ) = GlobalTheory.WeilM.hTens c JA JB₁ z z' := by
  rw [hTens_eq_trace', hTens_eq_trace']
  have hm : (z' * ιᵀ).map c = z'.map c * (ι.map c)ᵀ := by
    rw [← Matrix.transpose_map]; exact Matrix.map_mul (f := c.toRingHom)
  have ht : (ι.map c)ᵀ * JBᵀ * ι = JB₁ᵀ := by
    rw [← h, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [hm, Matrix.transpose_mul, Matrix.transpose_transpose]
  calc (ι * zᵀ * JA * (z'.map c * (ι.map c)ᵀ) * JBᵀ).trace
      = (ι * (zᵀ * JA * z'.map c * (ι.map c)ᵀ * JBᵀ)).trace := by simp only [Matrix.mul_assoc]
    _ = (zᵀ * JA * z'.map c * (ι.map c)ᵀ * JBᵀ * ι).trace := Matrix.trace_mul_comm _ _
    _ = (zᵀ * JA * z'.map c * ((ι.map c)ᵀ * JBᵀ * ι)).trace := by simp only [Matrix.mul_assoc]
    _ = (zᵀ * JA * z'.map c * JB₁ᵀ).trace := by rw [ht]

theorem symp_embed_eq : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (B : Base F E)
    {n d d₁ : ℕ} (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (JX : Matrix (Fin n) (Fin n) E),
    H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ z z' : Matrix (Fin n) (Fin d₁) (AE F E),
    symp (R := AF F) (cA σ) (-1) (incM F JX) (incM F W.J) (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ)
      (incM F (1 : Matrix (Fin n) (Fin n) E) * z' * (incM F H'.ι)ᵀ) =
    symp (R := AF F) (cA σ) (-1) (incM F JX) (incM F W₁.J) z z' := by
  intro F E _ _ _ _ _ σ B n d d₁ W W₁ H' i₀ i₁ JX hH z z'
  have hι : (incM F H'.ι).map (cA σ) = incM F (H'.ι.map σ) := by
    ext i j
    simp [incM, cA, inclR]
  have hg : (incM F H'.ι)ᵀ * incM F W.J * (incM F H'.ι).map (cA σ) = incM F W₁.J := by
    rw [hι, ← hH.gram]
    simp only [incM, Matrix.map_mul, Matrix.transpose_map]
  have h1 : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := by
    simp [incM]
  unfold symp
  rw [h1, Matrix.one_mul, Matrix.one_mul, hTens_embed (cA σ) _ _ _ _ hg]

end GlobalTheory.SympRestrict
