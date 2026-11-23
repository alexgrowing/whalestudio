import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarMemAdelicSchwartzSpaceNumberField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMapApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvaluationGoodModelsIntertwineStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TameConjMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TamePartRightStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TamePartLeftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelEigenRankOneVecMulVecStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMapPartRightEquivariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagFormBoxStarNeZeroStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory

open GlobalTheory.DoublingEv

theorem doubledEv_form : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      ∀ e, IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
      (∃ Φ ∈ schA F (Fin n × Fin d), e Φ ≠ 0) →
      ∀ (d' : Darboux (symp (R := AF F) (cA σ) (-1) (incM F W.J) (incM F X.J)) (Fin n × Fin d)),
      (∀ x : Matrix (Fin n) (Fin d) (AE F E), d'.e xᵀ = M.co.e x) →
      ∀ (dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F W.J) (dbl (incM F X.J))) ((Fin n × Fin d) ⊕ (Fin n × Fin d))),
      IsDblCoord (cA σ) (-1) (incM F W.J) (incM F X.J) d' dd →
      ∃ l ∈ (adeleClass F).adm ((Fin n × Fin d) ⊕ (Fin n × Fin d)),
        (∀ (y₁ y₂ : Fin d → AE F E) (u : Matrix (Fin d) (Fin n₁) (AE F E)), ∀ φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)),
          l (dd.rho B.ψ (Matrix.fromCols (Matrix.vecMulVec y₁ (incV F H.x) + u * (incM F H.ι)ᵀ)
            (Matrix.vecMulVec y₂ (incV F H.x) + u * (incM F H.ι)ᵀ)) φ) = l φ) ∧
        (∀ φ₁ ∈ schA F (Fin n × Fin d), ∀ φ₁' ∈ schA F (Fin n × Fin d), ∀ φ₂ ∈ schA F (Fin n × Fin d), ∀ c : ℂ,
          e φ₁' = c • e φ₁ → l (boxFun φ₁' φ₂) = c * l (boxFun φ₁ φ₂)) ∧
        ∃ φ₁ ∈ schA F (Fin n × Fin d), ∃ φ₂ ∈ schA F (Fin n × Fin d), l (boxFun φ₁ φ₂) ≠ 0 := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he hne d' hd' dd hdd
  have hψ : ∀ x, ‖B.ψ x‖ = 1 := GlobalTheory.StdCharFromIsStd.norm_psi hP.base.std
  have hT : IsTame F e := GlobalTheory.T.evaluation_good_models_intertwine F E σ B n d n₁ d X W X₁ W M M₁ H.ι 1 _ e hP.good hP₁.good he
  have hR : IsTame F (partR (κ := Fin n × Fin d) (conjMap e)) := GlobalTheory.T.tame_part_right F _ _ _ _ (GlobalTheory.T.tame_conj_map F _ _ e hT)
  have hL : IsTame F (partL (κ' := Fin n₁ × Fin d) e) := GlobalTheory.T.tame_part_left F _ _ _ e hT
  have hE : IsTame F (evDbl e) := hR.comp hL
  refine ⟨GlobalTheory.DiagForm.lDiag F _ ∘ₗ evDbl e, hE.comp_adm GlobalTheory.DiagForm.lDiag_adm, ?_, ?_, ?_⟩
  · intro y₁ y₂ u φ hφ
    have hd'' : ∀ w : Matrix (Fin d) (Fin n) (AE F E), d'.e w = M.co.e wᵀ := fun w => by
      rw [← hd' wᵀ, Matrix.transpose_transpose]
    have ht : ∀ y : Fin d → AE F E, (Matrix.vecMulVec y (incV F H.x) + u * (incM F H.ι)ᵀ)ᵀ =
        Matrix.vecMulVec (incV F H.x) y + incM F H.ι * uᵀ := fun y => by
      rw [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_vecMulVec]
    have key : dd.rho B.ψ (Matrix.fromCols (Matrix.vecMulVec y₁ (incV F H.x) + u * (incM F H.ι)ᵀ)
        (Matrix.vecMulVec y₂ (incV F H.x) + u * (incM F H.ι)ᵀ)) φ =
        schr B.ψ (Sum.elim (M.co.e (Matrix.vecMulVec (incV F H.x) y₁ + incM F H.ι * uᵀ)).1
            (M.co.e (Matrix.vecMulVec (incV F H.x) y₂ + incM F H.ι * uᵀ)).1,
          Sum.elim (M.co.e (Matrix.vecMulVec (incV F H.x) y₁ + incM F H.ι * uᵀ)).2
            (-(M.co.e (Matrix.vecMulVec (incV F H.x) y₂ + incM F H.ι * uᵀ)).2)) φ := by
      rw [Darboux.rho, hdd, hd'', hd'', ht, ht]
    have hlaw := GlobalTheory.T.model_eigen_rank_one_vecMulVec F E σ B n d X W M hP.base.std n₁ X₁ H j₀ j₁ M₁ hH e he
    rw [LinearMap.comp_apply, LinearMap.comp_apply, key,
      GlobalTheory.T.conj_map_part_right_equivariant F B.ψ hψ _ _ e (M.co.e (Matrix.vecMulVec (incV F H.x) y₁ + incM F H.ι * uᵀ)).1
        (M.co.e (Matrix.vecMulVec (incV F H.x) y₁ + incM F H.ι * uᵀ)).2 (M.co.e (Matrix.vecMulVec (incV F H.x) y₂ + incM F H.ι * uᵀ)).1
        (M.co.e (Matrix.vecMulVec (incV F H.x) y₂ + incM F H.ι * uᵀ)).2 (M₁.co.e uᵀ).1 (M₁.co.e uᵀ).2
        (fun Φ hΦ => hlaw y₁ u Φ hΦ) (fun Φ hΦ => hlaw y₂ u Φ hΦ) hR.mapsTo φ hφ,
      GlobalTheory.DiagForm.lDiag_schr B.ψ _ _ (hE.mapsTo φ hφ)]
  · intro φ₁ _ φ₁' _ φ₂ _ c hc
    simp only [LinearMap.comp_apply, evDbl_boxFun, hc, GlobalTheory.SchwartzBox.boxFun_smul_left, map_smul, smul_eq_mul]
  · obtain ⟨Φ, hΦ, hne⟩ := hne
    refine ⟨Φ, hΦ, star Φ, GlobalTheory.SchAConj.star_mem_schA F _ Φ hΦ, ?_⟩
    rw [LinearMap.comp_apply, evDbl_boxFun, conjMap_apply, star_star]
    exact GlobalTheory.T.diag_form_box_star_ne_zero F _ (e Φ) (he.maps Φ hΦ) hne

end GlobalTheory
