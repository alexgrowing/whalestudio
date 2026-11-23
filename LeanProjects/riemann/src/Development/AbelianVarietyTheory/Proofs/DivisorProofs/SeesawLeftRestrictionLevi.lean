import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsDblOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlanePairRestrictionFirst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewAdaptedPairEigenUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneRestrictionIsPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerRestriction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarMemAdelicSchwartzSpaceNumberField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawLeftRestrictionUnipotentStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.MixXChar GlobalTheory.DblEval
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.MixXDblEv

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d n₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁}

theorem rho_tr (M : Model σ X W) {d' : Darboux (symp (cA σ) (-1) (incM F W.J) (incM F X.J)) (Fin n × Fin d)}
    (hd' : ∀ x, d'.e xᵀ = M.co.e x) (ψ : AddChar (AF F) ℂ) (w : Matrix (Fin d) (Fin n) (AE F E)) :
    d'.rho ψ w = M.co.rho ψ wᵀ := by
  show schr ψ (d'.e w) = schr ψ (M.co.e wᵀ)
  rw [← hd', Matrix.transpose_transpose]

section Law

variable {B : Base F E} {M : Model σ X W} {M₁ : Model σ X₁ W} {χX χW : Chr F E} {om : Rep σ X W}
    {r s r' s' j₀ j₁ : ℕ} {H : Plane E n n₁} {e : Fn F n d →ₗ[ℂ] Fn F n₁ d}
    (hP : IsPair B M χX χW om r s r' s') (hH : H.IsAdapted σ B X X₁ j₀ j₁)
    (he : IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e)
include hP hH he

theorem law_one (z : Matrix (Fin n₁) (Fin d) (AE F E)) (y : Fin d → AE F E) :
    ∀ φ ∈ schA F (Fin n × Fin d),
      e (M.co.rho B.ψ (incM F H.ι * z + Matrix.vecMulVec (incV F H.x) y) φ) = M₁.co.rho B.ψ z (e φ) := by
  intro φ hφ
  have hone : incM F H.ι * z = incM F H.ι * z * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ := by
    rw [GlobalTheory.MixedLagrX.incM_one, Matrix.transpose_one, Matrix.mul_one]
  have horth : symp (cA σ) (-1) (incM F X.J) (incM F W.J) (incM F H.ι * z) (Matrix.vecMulVec (incV F H.x) y) = 0 := by
    rw [hone]; exact GlobalTheory.MixedLagrX.symp_eq_zero _ _ _ _ (GlobalTheory.MixedLagrX.piece_ix hH z y)
  rw [GlobalTheory.UnipEvLaw.rho_add M B.ψ _ _ horth, hone,
    he.Heisenberg₂ z _ (GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hP.base.std _ _ hφ), he.inv _ ⟨y, rfl⟩ φ hφ]

theorem law_two (z : Matrix (Fin n₁) (Fin d) (AE F E)) (y : Fin d → AE F E) :
    ∀ φ ∈ schA F (Fin n × Fin d),
      conjLin e (M.co.rho B.ψ⁻¹ (incM F H.ι * z + Matrix.vecMulVec (incV F H.x) y) φ) =
        M₁.co.rho B.ψ⁻¹ z (conjLin e φ) := by
  intro φ hφ
  have hψ : ∀ t, ‖B.ψ t‖ = 1 := GlobalTheory.StdCharWeilDatum.norm_psi hP.base.std
  funext x'
  rw [conjLin_apply]
  have h1 : (fun x => starRingEnd ℂ (M.co.rho B.ψ⁻¹ (incM F H.ι * z + Matrix.vecMulVec (incV F H.x) y) φ x)) =
      M.co.rho B.ψ (incM F H.ι * z + Matrix.vecMulVec (incV F H.x) y) (fun x => starRingEnd ℂ (φ x)) :=
    funext fun x => conj_schr_inv B.ψ hψ _ _ _
  have hs : (fun x => starRingEnd ℂ (φ x)) ∈ schA F (Fin n × Fin d) := GlobalTheory.SchAConj.star_mem_schA F _ φ hφ
  rw [h1, law_one hP hH he z y _ hs]
  exact conj_schr B.ψ hψ _ _ _

end Law

theorem dbl_decomp (H : Plane E n n₁) (w : Matrix (Fin d) (Fin n₁ ⊕ Fin n₁) (AE F E)) (z₁ z₂ : Fin d → AE F E) :
    w * (dblEmb (F := F) H.ι)ᵀ + (Matrix.vecMulVec z₁ (Sum.elim (incV F H.x) (0 : Fin n → AE F E)) +
      Matrix.vecMulVec z₂ (Sum.elim (0 : Fin n → AE F E) (incV F H.x))) =
    Matrix.fromCols (w.toCols₁ * (incM F H.ι)ᵀ + Matrix.vecMulVec z₁ (incV F H.x))
      (w.toCols₂ * (incM F H.ι)ᵀ + Matrix.vecMulVec z₂ (incV F H.x)) := by
  ext i j
  rcases j with j | j <;>
    simp [dblEmb, Matrix.mul_apply, Matrix.fromBlocks_transpose, Fintype.sum_sum_type, Matrix.vecMulVec_apply,
      Matrix.fromBlocks]

end GlobalTheory.MixXDblEv

namespace GlobalTheory.MixXDblEv

theorem exists_dblEv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      ∀ e, IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
      ∀ dd omd dd₁ omd₁, IsDblOf B.ψ M χW om dd omd → IsDblOf B.ψ M₁ χW om₁ dd₁ omd₁ →
      ∃ (et : ((((Fin n × Fin d) ⊕ (Fin n × Fin d)) → AF F) → ℂ) →ₗ[ℂ] ((((Fin n₁ × Fin d) ⊕ (Fin n₁ × Fin d)) → AF F) → ℂ)) (e₂ : Fn F n d →ₗ[ℂ] Fn F n₁ d),
        (∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)), et Φ ∈ schA F ((Fin n₁ × Fin d) ⊕ (Fin n₁ × Fin d))) ∧
        (∀ φ ∈ schA F (Fin n × Fin d), e₂ φ ∈ schA F (Fin n₁ × Fin d)) ∧
        (∃ φ ∈ schA F (Fin n × Fin d), e₂ φ ≠ 0) ∧
        (∀ φ₁ ∈ schA F (Fin n × Fin d), ∀ φ₂ ∈ schA F (Fin n × Fin d), et (boxFun φ₁ φ₂) = boxFun (e φ₁) (e₂ φ₂)) ∧
        (∀ w : Matrix (Fin d) (Fin n₁ ⊕ Fin n₁) (AE F E), ∀ u ∈ isoD d H, ∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)),
          et (dd.rho B.ψ (w * (dblEmb H.ι)ᵀ + u) Φ) = dd₁.rho B.ψ w (et Φ)) ∧
        (∀ l ∈ (adeleClass F).adm ((Fin n₁ × Fin d) ⊕ (Fin n₁ × Fin d)), l ∘ₗ et ∈ (adeleClass F).adm ((Fin n × Fin d) ⊕ (Fin n × Fin d))) ∧
        (∀ l ∈ (adeleClass F).adm ((Fin n₁ × Fin d) ⊕ (Fin n₁ × Fin d)),
          (∀ z : Matrix (Fin d) (Fin n₁) (AE F E), ∀ φ ∈ schA F ((Fin n₁ × Fin d) ⊕ (Fin n₁ × Fin d)), l (dd₁.rho B.ψ (z * ((diagCols (Fin n₁) : Matrix (Fin n₁ ⊕ Fin n₁) (Fin n₁) (AE F E)))ᵀ) φ) = l φ) →
          (∃ φ ∈ schA F ((Fin n₁ × Fin d) ⊕ (Fin n₁ × Fin d)), l φ ≠ 0) → ∃ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)), l (et Φ) ≠ 0) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he dd omd dd₁ omd₁ hD hD₁
  have hD' := hD
  have hD₁' := hD₁
  obtain ⟨d', hd', hdc, -, -⟩ := hD'
  obtain ⟨d₁', hd₁', hdc₁, -, -⟩ := hD₁'
  have hL : IsLocOp e := isLocOp_of_isEv hP.good hP₁.good he
  have hL₂ : IsLocOp (conjLin e) := GlobalTheory.T.conj_local_operator e hL
  have lawL : ∀ (w₁ : Matrix (Fin d) (Fin n₁) (AE F E)) (z₁ : Fin d → AE F E), ∀ φ ∈ schA F (Fin n × Fin d),
      e (d'.rho B.ψ (w₁ * (incM F H.ι)ᵀ + Matrix.vecMulVec z₁ (incV F H.x)) φ) = d₁'.rho B.ψ w₁ (e φ) := by
    intro w₁ z₁ φ hφ
    rw [rho_tr M hd', rho_tr M₁ hd₁', Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_vecMulVec]
    exact law_one hP hH he _ _ φ hφ
  have lawR : ∀ (w₂ : Matrix (Fin d) (Fin n₁) (AE F E)) (z₂ : Fin d → AE F E), ∀ φ ∈ schA F (Fin n × Fin d),
      conjLin e (d'.rho B.ψ⁻¹ (w₂ * (incM F H.ι)ᵀ + Matrix.vecMulVec z₂ (incV F H.x)) φ) =
        d₁'.rho B.ψ⁻¹ w₂ (conjLin e φ) := by
    intro w₂ z₂ φ hφ
    rw [rho_tr M hd', rho_tr M₁ hd₁', Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_vecMulVec]
    exact law_two hP hH he _ _ φ hφ
  obtain ⟨Φ₀, h₀, hne⟩ := GlobalTheory.EvSchANe.exists_mem_schA_ne_zero F E σ B n d n₁ d X W X₁ W M M₁ H.ι 1 _ e hP.good
    hP₁.good he
  refine ⟨partRₗ (conjLin e) ∘ₗ partLₗ e, conjLin e, fun Φ hΦ => ?_, fun φ hφ => ?_, ?_, fun φ₁ _ φ₂ _ => ?_,
    fun w u hu Φ hΦ => ?_, fun l hl => ?_, fun l hl hinv hl0 => ?_⟩
  · exact partR_mem (conjLin e) hL₂ _ (partL_mem e hL Φ hΦ)
  · have hs : (fun x => starRingEnd ℂ (φ x)) ∈ schA F (Fin n × Fin d) := GlobalTheory.SchAConj.star_mem_schA F _ φ hφ
    exact GlobalTheory.SchAConj.star_mem_schA F _ _ (he.maps _ hs)
  · have hs : (fun x => starRingEnd ℂ (Φ₀ x)) ∈ schA F (Fin n × Fin d) := GlobalTheory.SchAConj.star_mem_schA F _ Φ₀ h₀
    refine ⟨fun x => starRingEnd ℂ (Φ₀ x), hs, fun h => hne (funext fun y => ?_)⟩
    have := congrFun h y
    simpa [conjLin_apply] using this
  · funext y
    simp only [LinearMap.comp_apply, partLₗ_apply, partRₗ_apply, partR, partL, boxFun, Sum.elim_comp_inl,
      Sum.elim_comp_inr]
    have h1 : (fun x => e (fun x' => φ₁ x' * φ₂ x) (y ∘ Sum.inl)) = e φ₁ (y ∘ Sum.inl) • φ₂ := funext fun x => by
      rw [show (fun x' => φ₁ x' * φ₂ x) = φ₂ x • φ₁ from funext fun x' => by simp [mul_comm], map_smul]
      simp [mul_comm]
    rw [h1, map_smul]
    rfl
  · obtain ⟨z₁, z₂, rfl⟩ := hu
    erw [dbl_decomp (F := F) H w z₁ z₂]
    rw [rho_dbl _ _ _ _ _ _ hdc]
    conv_rhs => rw [← Matrix.fromCols_toCols w, rho_dbl _ _ _ _ _ _ hdc₁]
    simp only [LinearMap.comp_apply, partLₗ_apply, partRₗ_apply]
    rw [partL_intertwine e (d'.rho B.ψ (w.toCols₁ * (incM F H.ι)ᵀ + Matrix.vecMulVec z₁ (incV F H.x)))
        (d₁'.rho B.ψ w.toCols₁) e _ (fun φ hφ => lawL _ _ φ hφ)
        (fun b => by rw [sliceL_partR_rho]; exact Submodule.smul_mem _ _ (sliceL_mem hΦ _)),
      partL_partR_rho, partR_partL_rho,
      partR_intertwine (conjLin e) (d'.rho B.ψ⁻¹ (w.toCols₂ * (incM F H.ι)ᵀ + Matrix.vecMulVec z₂ (incV F H.x)))
        (d₁'.rho B.ψ⁻¹ w.toCols₂) (conjLin e) _ (fun φ hφ => lawR _ _ φ hφ)
        (fun a => sliceR_mem (partL_mem e hL Φ hΦ) a)]
  · rw [← LinearMap.comp_assoc]
    exact partL_adm e hL _ (partR_adm (conjLin e) hL₂ l hl)
  · exact GlobalTheory.T.seesaw_left_restriction_unipotent F E σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he dd omd dd₁ omd₁ hD hD₁
      l hl hinv hl0

end GlobalTheory.MixXDblEv
