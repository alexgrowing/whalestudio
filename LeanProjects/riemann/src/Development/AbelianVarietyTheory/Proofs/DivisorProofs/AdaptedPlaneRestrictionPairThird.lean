import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjLinApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlanePairRestrictionFirst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzConjMemStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjLocalOperatorStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.DblEvalW

theorem fromCols_mul_blockDiag_transpose {R : Type} [CommRing R] {m a b : Type} [Fintype a] [Fintype b]
    (z₁ z₂ : Matrix m b R) (A : Matrix a b R) :
    Matrix.fromCols z₁ z₂ * (Matrix.fromBlocks A 0 0 A)ᵀ = Matrix.fromCols (z₁ * Aᵀ) (z₂ * Aᵀ) := by
  rw [Matrix.fromBlocks_transpose, Matrix.transpose_zero]
  ext i j
  cases j <;> simp [Matrix.mul_apply, Matrix.fromCols, Matrix.fromBlocks, Fintype.sum_sum_type]

theorem exists_dblEv : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ → ∀ e, IsEv B M M₁ 1 H'.ι (iso0 n H') e →
      ∀ (dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (dbl (incM F W.J))) (Fin n × Fin d ⊕ Fin n × Fin d))
        (dd₁ : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (dbl (incM F W₁.J))) (Fin n × Fin d₁ ⊕ Fin n × Fin d₁)),
        IsDblCoord (cA σ) (-1) (incM F X.J) (incM F W.J) M.co dd → IsDblCoord (cA σ) (-1) (incM F X.J) (incM F W₁.J) M₁.co dd₁ →
      ∃ (Ed : ((Fin n × Fin d ⊕ Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ((Fin n × Fin d₁ ⊕ Fin n × Fin d₁ → AF F) → ℂ))
        (e₂ : Fn F n d →ₗ[ℂ] Fn F n d₁),
        (∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), Ed Φ ∈ schA F (Fin n × Fin d₁ ⊕ Fin n × Fin d₁)) ∧
        (∀ (z : Matrix (Fin n) (Fin d₁ ⊕ Fin d₁) (AE F E)), ∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d),
          Ed (dd.rho B.ψ (z * (Matrix.fromBlocks (incM F H'.ι) 0 0 (incM F H'.ι))ᵀ) Φ) = dd₁.rho B.ψ z (Ed Φ)) ∧
        (∀ (y : Fin n → AE F E), ∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d),
          Ed (dd.rho B.ψ (Matrix.fromCols (Matrix.vecMulVec y (incV F H'.x)) 0) Φ) = Ed Φ ∧
          Ed (dd.rho B.ψ (Matrix.fromCols 0 (Matrix.vecMulVec y (incV F H'.x))) Φ) = Ed Φ) ∧
        (∀ l ∈ (adeleClass F).adm (Fin n × Fin d₁ ⊕ Fin n × Fin d₁), l ∘ₗ Ed ∈ (adeleClass F).adm (Fin n × Fin d ⊕ Fin n × Fin d)) ∧
        (∀ Φ₁ ∈ schA F (Fin n × Fin d), ∀ Φ₂ ∈ schA F (Fin n × Fin d), Ed (boxFun Φ₁ Φ₂) = boxFun (e Φ₁) (e₂ Φ₂)) ∧
        (∀ Φ ∈ schA F (Fin n × Fin d), e₂ Φ ∈ schA F (Fin n × Fin d₁)) ∧
        ∃ Φ ∈ schA F (Fin n × Fin d), e₂ Φ ≠ 0 := by
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hpair d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ _ hpair₁ e he dd dd₁ hdd hdd₁
  have hψ : ∀ t, ‖B.ψ t‖ = 1 := GlobalTheory.StdCharWeilDatum.norm_psi hpair.base.std
  have hL : IsLocOp e := isLocOp_of_isEv hpair.good hpair₁.good he
  have hL₂ : IsLocOp (conjLin e) := GlobalTheory.T.conj_local_operator e hL
  have hone : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := by
    rw [incM, Matrix.map_one _ (map_zero _) (map_one _)]
  set A := incM F H'.ι with hA
  have Heisenberg₂ : ∀ (z : Matrix (Fin n) (Fin d₁) (AE F E)), ∀ φ ∈ schA F (Fin n × Fin d),
      e (M.co.rho B.ψ (z * Aᵀ) φ) = M₁.co.rho B.ψ z (e φ) := fun z φ hφ => by
    have := he.Heisenberg₂ z φ hφ
    rwa [hone, Matrix.one_mul] at this
  have heis₂ : ∀ (z : Matrix (Fin n) (Fin d₁) (AE F E)), ∀ φ ∈ schA F (Fin n × Fin d),
      conjLin e (M.co.rho B.ψ⁻¹ (z * Aᵀ) φ) = M₁.co.rho B.ψ⁻¹ z (conjLin e φ) := fun z φ hφ => by
    funext y
    rw [conjLin_apply]
    have h1 : (fun x => starRingEnd ℂ (M.co.rho B.ψ⁻¹ (z * Aᵀ) φ x)) =
        M.co.rho B.ψ (z * Aᵀ) (fun x => starRingEnd ℂ (φ x)) :=
      funext fun x => conj_schr_inv B.ψ hψ _ _ _
    rw [h1, Heisenberg₂ z _ (GlobalTheory.T.adelic_schwartz_conj_mem φ hφ)]
    exact conj_schr B.ψ hψ _ _ _
  have inv₁ : ∀ (y : Fin n → AE F E), ∀ φ ∈ schA F (Fin n × Fin d),
      e (M.co.rho B.ψ (Matrix.vecMulVec y (incV F H'.x)) φ) = e φ := fun y φ hφ => he.inv _ ⟨y, rfl⟩ φ hφ
  have inv₂ : ∀ (y : Fin n → AE F E), ∀ φ ∈ schA F (Fin n × Fin d),
      conjLin e (M.co.rho B.ψ⁻¹ (Matrix.vecMulVec y (incV F H'.x)) φ) = conjLin e φ := fun y φ hφ => by
    funext x'
    rw [conjLin_apply, conjLin_apply]
    have h1 : (fun x => starRingEnd ℂ (M.co.rho B.ψ⁻¹ (Matrix.vecMulVec y (incV F H'.x)) φ x)) =
        M.co.rho B.ψ (Matrix.vecMulVec y (incV F H'.x)) (fun x => starRingEnd ℂ (φ x)) :=
      funext fun x => conj_schr_inv B.ψ hψ _ _ _
    rw [h1, inv₁ y _ (GlobalTheory.T.adelic_schwartz_conj_mem φ hφ)]
  have invB : ∀ (y₁ y₂ : Fin n → AE F E), ∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d),
      (partRₗ (conjLin e) ∘ₗ partLₗ e) (dd.rho B.ψ (Matrix.fromCols (Matrix.vecMulVec y₁ (incV F H'.x))
        (Matrix.vecMulVec y₂ (incV F H'.x))) Φ) = (partRₗ (conjLin e) ∘ₗ partLₗ e) Φ := fun y₁ y₂ Φ hΦ => by
    rw [rho_dbl _ _ _ _ _ _ hdd]
    simp only [LinearMap.comp_apply, partLₗ_apply, partRₗ_apply]
    rw [partL_intertwine e (M.co.rho B.ψ (Matrix.vecMulVec y₁ (incV F H'.x))) (fun φ => φ) e _
        (fun φ hφ => inv₁ _ φ hφ) (fun b => by rw [sliceL_partR_rho]; exact Submodule.smul_mem _ _ (sliceL_mem hΦ _)),
      partL_id, partL_partR_rho,
      partR_intertwine (conjLin e) (M.co.rho B.ψ⁻¹ (Matrix.vecMulVec y₂ (incV F H'.x))) (fun φ => φ) (conjLin e) _
        (fun φ hφ => inv₂ _ φ hφ) (fun a => sliceR_mem (partL_mem e hL Φ hΦ) a), partR_id]
  refine ⟨partRₗ (conjLin e) ∘ₗ partLₗ e, conjLin e, fun Φ hΦ => ?_, fun z Φ hΦ => ?_, fun y Φ hΦ => ?_,
    fun l hl => ?_, fun φ₁ _ φ₂ _ => ?_, fun φ hφ => ?_, ?_⟩
  · exact partR_mem (conjLin e) hL₂ _ (partL_mem e hL Φ hΦ)
  · rw [← Matrix.fromCols_toCols z, fromCols_mul_blockDiag_transpose, rho_dbl _ _ _ _ _ _ hdd,
      rho_dbl _ _ _ _ _ _ hdd₁]
    simp only [LinearMap.comp_apply, partLₗ_apply, partRₗ_apply]
    rw [partL_intertwine e (M.co.rho B.ψ (z.toCols₁ * Aᵀ)) (M₁.co.rho B.ψ z.toCols₁) e _ (fun φ hφ => Heisenberg₂ _ φ hφ)
        (fun b => by rw [sliceL_partR_rho]; exact Submodule.smul_mem _ _ (sliceL_mem hΦ _)),
      partL_partR_rho, partR_partL_rho,
      partR_intertwine (conjLin e) (M.co.rho B.ψ⁻¹ (z.toCols₂ * Aᵀ)) (M₁.co.rho B.ψ⁻¹ z.toCols₂) (conjLin e) _
        (fun φ hφ => heis₂ _ φ hφ) (fun a => sliceR_mem (partL_mem e hL Φ hΦ) a)]
  · have h0 : (0 : Matrix (Fin n) (Fin d) (AE F E)) = Matrix.vecMulVec 0 (incV F H'.x) := by
      ext i j; simp [Matrix.vecMulVec_apply]
    refine ⟨?_, ?_⟩
    · rw [h0]; exact invB y 0 Φ hΦ
    · rw [h0]; exact invB 0 y Φ hΦ
  · rw [← LinearMap.comp_assoc]
    exact partL_adm e hL _ (partR_adm (conjLin e) hL₂ l hl)
  · funext y
    simp only [LinearMap.comp_apply, partLₗ_apply, partRₗ_apply, partR, partL, boxFun, Sum.elim_comp_inl,
      Sum.elim_comp_inr]
    have h1 : (fun x => e (fun x' => φ₁ x' * φ₂ x) (y ∘ Sum.inl)) = e φ₁ (y ∘ Sum.inl) • φ₂ := funext fun x => by
      rw [show (fun x' => φ₁ x' * φ₂ x) = φ₂ x • φ₁ from funext fun x' => by simp [mul_comm], map_smul]
      simp [mul_comm]
    rw [h1, map_smul]
    rfl
  · exact GlobalTheory.T.adelic_schwartz_conj_mem _ (he.maps _ (GlobalTheory.T.adelic_schwartz_conj_mem φ hφ))
  · obtain ⟨Φ₀, h₀, hne⟩ := GlobalTheory.T.eigen_intertwiner_restriction F E σ B n d n d₁ X W X W₁ M M₁ 1 H'.ι (iso0 n H') e hpair.good hpair₁.good he
    refine ⟨fun x => starRingEnd ℂ (Φ₀ x), GlobalTheory.T.adelic_schwartz_conj_mem _ h₀, fun h => hne (funext fun y => ?_)⟩
    have := congrFun h y
    simpa [conjLin_apply] using this

end GlobalTheory.DblEvalW

end
