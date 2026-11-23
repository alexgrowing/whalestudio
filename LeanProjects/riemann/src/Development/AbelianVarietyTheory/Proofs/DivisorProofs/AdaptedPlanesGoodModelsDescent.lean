import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AtVecMulVecRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLagrangianSetArchimedean
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleAdaptedLagrangianEq
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ArchSch GlobalTheory.ArchSchB GlobalTheory.ArchSchA

noncomputable section

namespace GlobalTheory.ArchSchA

open GlobalTheory.ArchSchB.Iso in

theorem lagSetA_isotropic : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (B : Base F E) {n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁} (M : Model σ X W) (M₁ : Model σ X₁ W₁) (H : Plane E n n₁) (H' : Plane E d d₁),
    B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → H.IsAdapted σ B X X₁ j₀ j₁ → H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ l ∈ lagSetA M M₁ H H', ∀ l' ∈ lagSetA M M₁ H H', trP F _ l.1 l'.2 = trP F _ l'.1 l.2 := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ X W X₁ W₁ M M₁ H H' hB hX hW hH hH' l hl l' hl'
  obtain ⟨y, c, z, -, -, -, hz1, rfl⟩ := hl
  obtain ⟨y', c', z', -, -, -, hz1', rfl⟩ := hl'
  have hinv : ∀ t, σ (σ t) = t := fun t => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star]
  have hflipX : ∀ u v, form σ X.J u v = 0 → form σ X.J v u = 0 := fun u v h => by
    rw [form_herm hinv hX.herm, h, map_zero]
  have hflipW : ∀ u v, form σ W.J u v = 0 → form σ W.J v u = 0 := fun u v h => by
    rw [GlobalTheory.ArchSch.OrthPlane.form_swap hinv hW.skew, h, map_zero, neg_zero]
  have h0 : ∀ {p q : Type}, incM F (0 : Matrix p q E) = 0 := fun {p q} => by ext; simp [incM]
  have hXX : (incM F (Matrix.replicateCol Unit H.x))ᵀ * incM F X.J * (incM F (Matrix.replicateCol Unit H.x)).map (cA σ) = 0 := by
    rw [incM_gram, gram_xx hH, h0]
  have hXI : (incM F (Matrix.replicateCol Unit H.x))ᵀ * incM F X.J * (incM F H.ι).map (cA σ) = 0 := by
    rw [incM_gram, gram_xι hH hflipX, h0]
  have hIX : (incM F H.ι)ᵀ * incM F X.J * (incM F (Matrix.replicateCol Unit H.x)).map (cA σ) = 0 := by
    rw [incM_gram, gram_ιx hH, h0]
  have hWW : (incM F (Matrix.replicateCol Unit H'.x))ᵀ * incM F W.J * (incM F (Matrix.replicateCol Unit H'.x)).map (cA σ) = 0 := by
    rw [incM_gram, gram_xx hH', h0]
  have hWI : (incM F (Matrix.replicateCol Unit H'.x))ᵀ * incM F W.J * (incM F H'.ι).map (cA σ) = 0 := by
    rw [incM_gram, gram_xι hH' hflipW, h0]
  have hIW : (incM F H'.ι)ᵀ * incM F W.J * (incM F (Matrix.replicateCol Unit H'.x)).map (cA σ) = 0 := by
    rw [incM_gram, gram_ιx hH', h0]
  have hGX : (incM F H.ι)ᵀ * incM F X.J * (incM F H.ι).map (cA σ) = incM F X₁.J := by
    rw [incM_gram, hH.gram]
  have hGW : (incM F H'.ι)ᵀ * incM F W.J * (incM F H'.ι).map (cA σ) = incM F W₁.J := by
    rw [incM_gram, hH'.gram]
  have hA : ∀ y : Fin n → AE F E, Matrix.vecMulVec y (incV F H'.x) =
      (1 : Matrix (Fin n) (Fin n) (AE F E)) * Matrix.replicateCol Unit y *
        (incM F (Matrix.replicateCol Unit H'.x))ᵀ := by
    intro y
    rw [Matrix.one_mul, Matrix.vecMulVec_eq Unit]
    congr 1
  have hC : ∀ c : Fin d₁ → AE F E, Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ c) =
      incM F (Matrix.replicateCol Unit H.x) * Matrix.replicateRow Unit c * (incM F H'.ι)ᵀ := by
    intro c
    ext i j
    simp [Matrix.vecMulVec_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct, incM, incV, Matrix.replicateCol_apply,
      Matrix.replicateRow_apply, Finset.mul_sum, mul_comm, mul_left_comm]
  have key : symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)
      (Matrix.vecMulVec y (incV F H'.x) + Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ c) + incM F H.ι * z * (incM F H'.ι)ᵀ)
      (Matrix.vecMulVec y' (incV F H'.x) + Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ c') + incM F H.ι * z' * (incM F H'.ι)ᵀ) =
      symp (R := AF F) (cA σ) (-1) (incM F X₁.J) (incM F W₁.J) z z' := by
    simp only [lagL_dar_add_left M.co, lagL_dar_add_right M.co]
    rw [hA y, hA y', hC c, hC c']
    rw [symp_change_zero_right _ _ _ _ _ _ _ _ _ _ hWW, symp_change_zero_right _ _ _ _ _ _ _ _ _ _ hWI,
      symp_change_zero_right _ _ _ _ _ _ _ _ _ _ hWI, symp_change_zero_right _ _ _ _ _ _ _ _ _ _ hIW,
      symp_change_zero_left _ _ _ _ _ _ _ _ _ _ hXX, symp_change_zero_left _ _ _ _ _ _ _ _ _ _ hXI,
      symp_change_zero_right _ _ _ _ _ _ _ _ _ _ hIW, symp_change_zero_left _ _ _ _ _ _ _ _ _ _ hIX,
      symp_change_eq _ _ _ _ _ _ _ _ _ _ hGX hGW]
    simp only [zero_add, add_zero]
  rw [← sub_eq_zero, ← GlobalTheory.ArchSch.trace_evI_darboux M.co, key, GlobalTheory.ArchSch.trace_evI_darboux M₁.co, hz1, hz1']
  simp

end GlobalTheory.ArchSchA
