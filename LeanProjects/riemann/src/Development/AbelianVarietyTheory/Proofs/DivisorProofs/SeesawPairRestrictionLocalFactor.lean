import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjLinApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlanePairRestrictionFirst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzConjMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjLocalOperator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerTransitive

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.MixWOneDbl

theorem exists_dblEv0 : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ →
      ∀ (d' : Darboux (symp (cA σ) (-1) (incM F W.J) (incM F X.J)) (Fin n × Fin d)),
        (∀ x : Matrix (Fin n) (Fin d) (AE F E), d'.e xᵀ = M.co.e x) →
      ∀ (d₁' : Darboux (symp (cA σ) (-1) (incM F W₁.J) (incM F X.J)) (Fin n × Fin d₁)),
        (∀ x : Matrix (Fin n) (Fin d₁) (AE F E), d₁'.e xᵀ = M₁.co.e x) →
      ∀ (dd : Darboux (symp (cA σ) (-1) (incM F W.J) (dbl (incM F X.J))) ((Fin n × Fin d) ⊕ (Fin n × Fin d))),
        IsDblCoord (cA σ) (-1) (incM F W.J) (incM F X.J) d' dd →
      ∀ (dd₁ : Darboux (symp (cA σ) (-1) (incM F W₁.J) (dbl (incM F X.J))) ((Fin n × Fin d₁) ⊕ (Fin n × Fin d₁))),
        IsDblCoord (cA σ) (-1) (incM F W₁.J) (incM F X.J) d₁' dd₁ →
      ∀ e, IsEv B M M₁ 1 H'.ι (iso0 n H') e →
      ∃ ed : (((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) → ℂ) →ₗ[ℂ] (((Fin n × Fin d₁) ⊕ (Fin n × Fin d₁) → AF F) → ℂ),
        (∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)), ed Φ ∈ schA F ((Fin n × Fin d₁) ⊕ (Fin n × Fin d₁))) ∧
        (∀ (z : Matrix (Fin d₁) (Fin n ⊕ Fin n) (AE F E)), ∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)),
          ed (dd.rho B.ψ (incM F H'.ι * z) Φ) = dd₁.rho B.ψ z (ed Φ)) ∧
        (∀ (y : Fin n ⊕ Fin n → AE F E), ∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)),
          ed (dd.rho B.ψ (Matrix.vecMulVec (incV F H'.x) y) Φ) = ed Φ) ∧
        (∀ l ∈ (adeleClass F).adm ((Fin n × Fin d₁) ⊕ (Fin n × Fin d₁)), l ∘ₗ ed ∈ (adeleClass F).adm ((Fin n × Fin d) ⊕ (Fin n × Fin d))) ∧
        ∃ Φ₂ ∈ schA F (Fin n × Fin d), ∃ Ψ₂ ∈ schA F (Fin n × Fin d₁), Ψ₂ ≠ 0 ∧
          ∀ Φ₁ ∈ schA F (Fin n × Fin d), ed (boxFun Φ₁ Φ₂) = boxFun (e Φ₁) Ψ₂ := by
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hpair d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ _ hpair₁ d' hd' d₁' hd₁' dd hdd
    dd₁ hdd₁ e he
  have hψ : ∀ t, ‖B.ψ t‖ = 1 := GlobalTheory.StdCharWeilDatum.norm_psi hpair.base.std
  have hL : IsLocOp e := isLocOp_of_isEv hpair.good hpair₁.good he
  have hL₂ : IsLocOp (conjLin e) := GlobalTheory.DblEval.ConjLoc.isLocOp_conjLin e hL
  have hone : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := by
    rw [incM, Matrix.map_one _ (map_zero _) (map_one _)]
  have r0 : ∀ (ψ : AddChar (AF F) ℂ) (w : Matrix (Fin d) (Fin n) (AE F E)), d'.rho ψ w = M.co.rho ψ wᵀ := fun ψ w => by
    rw [Darboux.rho, Darboux.rho, ← hd', Matrix.transpose_transpose]
  have r1 : ∀ (ψ : AddChar (AF F) ℂ) (w : Matrix (Fin d₁) (Fin n) (AE F E)), d₁'.rho ψ w = M₁.co.rho ψ wᵀ := fun ψ w => by
    rw [Darboux.rho, Darboux.rho, ← hd₁', Matrix.transpose_transpose]
  have Heisenberg₂ : ∀ (z : Matrix (Fin d₁) (Fin n) (AE F E)), ∀ φ ∈ schA F (Fin n × Fin d),
      e (d'.rho B.ψ (incM F H'.ι * z) φ) = d₁'.rho B.ψ z (e φ) := fun z φ hφ => by
    have := he.Heisenberg₂ zᵀ φ hφ
    rw [hone, Matrix.one_mul] at this
    rw [r0, r1, Matrix.transpose_mul, this]
  have heis₂ : ∀ (z : Matrix (Fin d₁) (Fin n) (AE F E)), ∀ φ ∈ schA F (Fin n × Fin d),
      conjLin e (d'.rho B.ψ⁻¹ (incM F H'.ι * z) φ) = d₁'.rho B.ψ⁻¹ z (conjLin e φ) := fun z φ hφ => by
    funext y
    rw [conjLin_apply]
    have h1 : (fun x => starRingEnd ℂ (d'.rho B.ψ⁻¹ (incM F H'.ι * z) φ x)) =
        d'.rho B.ψ (incM F H'.ι * z) (fun x => starRingEnd ℂ (φ x)) :=
      funext fun x => conj_schr_inv B.ψ hψ _ _ _
    rw [h1, Heisenberg₂ z _ (GlobalTheory.ConjSch.conj_mem_schA φ hφ)]
    exact conj_schr B.ψ hψ _ _ _
  have inv₁ : ∀ (y : Fin n → AE F E), ∀ φ ∈ schA F (Fin n × Fin d),
      e (d'.rho B.ψ (Matrix.vecMulVec (incV F H'.x) y) φ) = e φ := fun y φ hφ => by
    have ht : (Matrix.vecMulVec (incV F H'.x) y)ᵀ = Matrix.vecMulVec y (incV F H'.x) := by
      ext i j; simp [Matrix.vecMulVec_apply, mul_comm]
    rw [r0, ht]
    exact he.inv _ ⟨y, rfl⟩ φ hφ
  have inv₂ : ∀ (y : Fin n → AE F E), ∀ φ ∈ schA F (Fin n × Fin d),
      conjLin e (d'.rho B.ψ⁻¹ (Matrix.vecMulVec (incV F H'.x) y) φ) = conjLin e φ := fun y φ hφ => by
    funext x'
    rw [conjLin_apply, conjLin_apply]
    have h1 : (fun x => starRingEnd ℂ (d'.rho B.ψ⁻¹ (Matrix.vecMulVec (incV F H'.x) y) φ x)) =
        d'.rho B.ψ (Matrix.vecMulVec (incV F H'.x) y) (fun x => starRingEnd ℂ (φ x)) :=
      funext fun x => conj_schr_inv B.ψ hψ _ _ _
    rw [h1, inv₁ y _ (GlobalTheory.ConjSch.conj_mem_schA φ hφ)]
  obtain ⟨Φ₀, h₀, hne⟩ := GlobalTheory.EvNonzero.exists_mem_schA_ev_ne_zero F E σ B n d n d₁ X W X W₁ M M₁ 1 H'.ι (iso0 n H') e
    hpair.good hpair₁.good he
  refine ⟨partRₗ (conjLin e) ∘ₗ partLₗ e, fun Φ hΦ => ?_, fun z Φ hΦ => ?_, fun z Φ hΦ => ?_,
    fun l hl => ?_, fun x => starRingEnd ℂ (Φ₀ x), GlobalTheory.ConjSch.conj_mem_schA _ h₀, conjLin e (fun x => starRingEnd ℂ (Φ₀ x)),
    GlobalTheory.ConjSch.conj_mem_schA _ (he.maps _ (GlobalTheory.ConjSch.conj_mem_schA _ (GlobalTheory.ConjSch.conj_mem_schA _ h₀))), fun h => hne (funext fun y => ?_),
    fun φ₁ _ => ?_⟩
  · exact partR_mem (conjLin e) hL₂ _ (partL_mem e hL Φ hΦ)
  · rw [← Matrix.fromCols_toCols z, Matrix.mul_fromCols, rho_dbl _ _ _ _ _ _ hdd, rho_dbl _ _ _ _ _ _ hdd₁]
    simp only [LinearMap.comp_apply, partLₗ_apply, partRₗ_apply]
    rw [partL_intertwine e (d'.rho B.ψ (incM F H'.ι * z.toCols₁)) (d₁'.rho B.ψ z.toCols₁) e _ (fun φ hφ => Heisenberg₂ _ φ hφ)
        (fun b => by rw [sliceL_partR_rho]; exact Submodule.smul_mem _ _ (sliceL_mem hΦ _)),
      partL_partR_rho, partR_partL_rho,
      partR_intertwine (conjLin e) (d'.rho B.ψ⁻¹ (incM F H'.ι * z.toCols₂)) (d₁'.rho B.ψ⁻¹ z.toCols₂) (conjLin e) _
        (fun φ hφ => heis₂ _ φ hφ) (fun a => sliceR_mem (partL_mem e hL Φ hΦ) a)]
  · have hv : Matrix.vecMulVec (incV F H'.x) z = Matrix.fromCols (Matrix.vecMulVec (incV F H'.x) (z ∘ Sum.inl))
        (Matrix.vecMulVec (incV F H'.x) (z ∘ Sum.inr)) := by
      ext i j; cases j <;> rfl
    rw [hv, rho_dbl _ _ _ _ _ _ hdd]
    simp only [LinearMap.comp_apply, partLₗ_apply, partRₗ_apply]
    rw [partL_intertwine e (d'.rho B.ψ (Matrix.vecMulVec (incV F H'.x) (z ∘ Sum.inl))) (fun φ => φ) e _
        (fun φ hφ => inv₁ _ φ hφ) (fun b => by rw [sliceL_partR_rho]; exact Submodule.smul_mem _ _ (sliceL_mem hΦ _)),
      partL_id, partL_partR_rho,
      partR_intertwine (conjLin e) (d'.rho B.ψ⁻¹ (Matrix.vecMulVec (incV F H'.x) (z ∘ Sum.inr))) (fun φ => φ) (conjLin e) _
        (fun φ hφ => inv₂ _ φ hφ) (fun a => sliceR_mem (partL_mem e hL Φ hΦ) a), partR_id]
  · rw [← LinearMap.comp_assoc]
    exact partL_adm e hL _ (partR_adm (conjLin e) hL₂ l hl)
  · have := congrFun h y
    simpa [conjLin_apply] using this
  · funext y
    simp only [LinearMap.comp_apply, partLₗ_apply, partRₗ_apply, partR, partL, boxFun, Sum.elim_comp_inl,
      Sum.elim_comp_inr]
    have h1 : (fun x => e (fun x' => φ₁ x' * (fun x => starRingEnd ℂ (Φ₀ x)) x) (y ∘ Sum.inl)) =
        e φ₁ (y ∘ Sum.inl) • (fun x => starRingEnd ℂ (Φ₀ x)) := funext fun x => by
      rw [show (fun x' => φ₁ x' * (fun x => starRingEnd ℂ (Φ₀ x)) x) = (fun x => starRingEnd ℂ (Φ₀ x)) x • φ₁ from
        funext fun x' => by simp [mul_comm], map_smul]
      simp [mul_comm]
    rw [h1, map_smul]
    rfl

end GlobalTheory.MixWOneDbl

end
