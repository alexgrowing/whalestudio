import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneRestrictionPairThird
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousGlueComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledSpaceDarbouxCharacterStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawPairRestrictionIsPairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittCharacterConjugateInverseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicModulusNormEqAbsStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.TorusLamP

open GlobalTheory.DblEval

theorem dblEv_props {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ) (hpair : IsPair B M χX χW om r s r' s')
    (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ)
    (hpair₁ : IsPair B M₁ χX χW om₁ r s r₁ s₁) (e : Fn F n d →ₗ[ℂ] Fn F n d₁) (he : IsEv B M M₁ 1 H'.ι (iso0 n H') e)
    (dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (dbl (incM F W.J))) (Fin n × Fin d ⊕ Fin n × Fin d))
    (dd₁ : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (dbl (incM F W₁.J))) (Fin n × Fin d₁ ⊕ Fin n × Fin d₁))
    (hdd : IsDblCoord (cA σ) (-1) (incM F X.J) (incM F W.J) M.co dd)
    (hdd₁ : IsDblCoord (cA σ) (-1) (incM F X.J) (incM F W₁.J) M₁.co dd₁) :
    (∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d),
        (partRₗ (conjLin e) ∘ₗ partLₗ e) Φ ∈ schA F (Fin n × Fin d₁ ⊕ Fin n × Fin d₁)) ∧
      (∀ (z : Matrix (Fin n) (Fin d₁ ⊕ Fin d₁) (AE F E)), ∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d),
        (partRₗ (conjLin e) ∘ₗ partLₗ e) (dd.rho B.ψ (z * (Matrix.fromBlocks (incM F H'.ι) 0 0 (incM F H'.ι))ᵀ) Φ) =
          dd₁.rho B.ψ z ((partRₗ (conjLin e) ∘ₗ partLₗ e) Φ)) ∧
      (∀ (y : Fin n → AE F E), ∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d),
        (partRₗ (conjLin e) ∘ₗ partLₗ e) (dd.rho B.ψ (Matrix.fromCols (Matrix.vecMulVec y (incV F H'.x)) 0) Φ) =
          (partRₗ (conjLin e) ∘ₗ partLₗ e) Φ ∧
        (partRₗ (conjLin e) ∘ₗ partLₗ e) (dd.rho B.ψ (Matrix.fromCols 0 (Matrix.vecMulVec y (incV F H'.x))) Φ) =
          (partRₗ (conjLin e) ∘ₗ partLₗ e) Φ) ∧
      (∀ l ∈ (adeleClass F).adm (Fin n × Fin d₁ ⊕ Fin n × Fin d₁),
        l ∘ₗ (partRₗ (conjLin e) ∘ₗ partLₗ e) ∈ (adeleClass F).adm (Fin n × Fin d ⊕ Fin n × Fin d)) ∧
      (∀ Φ₁ Φ₂ : Fn F n d, (partRₗ (conjLin e) ∘ₗ partLₗ e) (boxFun Φ₁ Φ₂) = boxFun (e Φ₁) (conjLin e Φ₂)) := by
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
  refine ⟨fun Φ hΦ => ?_, fun z Φ hΦ => ?_, fun y Φ hΦ => ?_, fun l hl => ?_, fun φ₁ φ₂ => ?_⟩
  · exact partR_mem (conjLin e) hL₂ _ (partL_mem e hL Φ hΦ)
  · rw [← Matrix.fromCols_toCols z, GlobalTheory.DblEvalW.fromCols_mul_blockDiag_transpose, rho_dbl _ _ _ _ _ _ hdd,
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

end GlobalTheory.TorusLamP

namespace GlobalTheory.TorusLamP

open GlobalTheory.DblEval

theorem levi_block' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {d : ℕ}
    (W : Spc F E d) (g : UA σ W.J) :
    ∃ gd : UG (cA σ) (dbl (incM F W.J)), gd.1.1 = Matrix.fromBlocks (mat g) 0 0 1 := by
  have h1 : mat g * mat g⁻¹ = 1 := by
    unfold mat; rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]; rfl
  have h2 : mat g⁻¹ * mat g = 1 := by
    unfold mat; rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]; rfl
  have hg : (mat g)ᵀ * incM F W.J * (mat g).map (cA σ) = incM F W.J := g.2
  refine ⟨⟨⟨Matrix.fromBlocks (mat g) 0 0 1, Matrix.fromBlocks (mat g⁻¹) 0 0 1, ?_, ?_⟩, ?_⟩, rfl⟩
  · rw [Matrix.fromBlocks_multiply]; simp [h1]
  · rw [Matrix.fromBlocks_multiply]; simp [h2]
  · show (Matrix.fromBlocks (mat g) 0 0 1)ᵀ * dbl (incM F W.J) * (Matrix.fromBlocks (mat g) 0 0 1).map (cA σ) = dbl (incM F W.J)
    have hm1 : (1 : Matrix (Fin d) (Fin d) (AE F E)).map (cA σ) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
    rw [Matrix.fromBlocks_transpose, dbl, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp [hm1, hg]

theorem exists_lam : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ → ∀ e, IsEv B M M₁ 1 H'.ι (iso0 n H') e →
      ∀ t m, IsLevi (W₁ := W₁) H' t 1 m →
        ∀ k : ℂ, (∀ Φ ∈ schA F (Fin n × Fin d), e (om (1, m) Φ) = k • e Φ) → (∃ Φ ∈ schA F (Fin n × Fin d), e Φ ≠ 0) →
      ∀ (dd : Darboux (symp (cA σ) (-1) (incM F X.J) (dbl (incM F W.J))) ((Fin n × Fin d) ⊕ (Fin n × Fin d)))
        (omd : UG (cA σ) (dbl (incM F W.J)) →* Module.End ℂ (((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) → ℂ)),
        IsDblCoord (cA σ) (-1) (incM F X.J) (incM F W.J) M.co dd →
        IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1) (incM F X.J) (dbl (incM F W.J)) dd χX (diagCols (Fin d)) omd →
        (∀ (g : UA σ W.J) (gd : UG (cA σ) (dbl (incM F W.J))),
          (gd.1.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) = Matrix.fromBlocks (mat g) 0 0 1 →
          ∀ φ₁ ∈ schA F (Fin n × Fin d), ∀ φ₂ ∈ schA F (Fin n × Fin d), omd gd (boxFun φ₁ φ₂) = boxFun (om (1, g) φ₁) φ₂) →
        ∀ p : UG (cA σ) (dbl (incM F W.J)),
          (p.1.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) = Matrix.fromBlocks (mat m) 0 0 1 * GlobalTheory.DblUnip.unipMat (cA σ).toRingHom (incM F W.J) (incV F H'.x) (incV F H'.y) ((↑t⁻¹ : AE F E) - 1) →
        ∃ Λ : (((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) → ℂ) →ₗ[ℂ] ℂ, Λ ∈ (adeleClass F).adm ((Fin n × Fin d) ⊕ (Fin n × Fin d)) ∧
          (∀ z : Matrix (Fin n) (Fin d) (AE F E), ∀ φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)),
            Λ (dd.rho B.ψ (z * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E))ᵀ) φ) = Λ φ) ∧
          (∀ φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)),
            Λ (omd p φ) = (k * (((absE F E t : ℝ) ^ (-(n : ℝ)) : ℝ) : ℂ)) * Λ φ) ∧
          ∃ φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)), Λ φ ≠ 0 := by
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hA hP₁ e he t m hm k hk hne
    dd omd hdc hspl hbox p hp
  have hstd : IsStd B.ψ := hP.base.std

  obtain ⟨⟨-, dd₁, -, hdd₁, -⟩, -⟩ := hP₁.weil
  obtain ⟨h1, h2, h3, h4, h5⟩ := dblEv_props σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' M₁ om₁ r₁ s₁ hP₁ e he dd dd₁
    hdc hdd₁
  set Ed := partRₗ (conjLin e) ∘ₗ partLₗ e with hEd
  set lam := DiagForm.lDiag F (Fin n × Fin d₁) ∘ₗ Ed with hlam
  have hlamx : ∀ x, lam x = DiagForm.lDiag F (Fin n × Fin d₁) (Ed x) := fun x => rfl
  have hadm : lam ∈ (adeleClass F).adm (Fin n × Fin d ⊕ Fin n × Fin d) := h4 _ DiagForm.lDiag_adm
  have hinvL : ∀ (y₁ y₂ : Fin n → AE F E) (Z : Matrix (Fin n) (Fin d₁) (AE F E)),
      ∀ Ψ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d),
        lam (dd.rho B.ψ (Matrix.fromCols (Matrix.vecMulVec y₁ (incV F H'.x) + Z * (incM F H'.ι)ᵀ)
          (Matrix.vecMulVec y₂ (incV F H'.x) + Z * (incM F H'.ι)ᵀ)) Ψ) = lam Ψ := by
    intro y₁ y₂ Z Ψ hΨ
    set P := Z * (incM F H'.ι)ᵀ with hPdef
    have hsplit : Matrix.fromCols (Matrix.vecMulVec y₁ (incV F H'.x) + P) (Matrix.vecMulVec y₂ (incV F H'.x) + P) =
        Matrix.fromCols (Matrix.vecMulVec y₁ (incV F H'.x)) 0 +
          (Matrix.fromCols 0 (Matrix.vecMulVec y₂ (incV F H'.x)) + Matrix.fromCols P P) := by
      ext i j; cases j <;> simp
    have hO : ∀ u, form σ W.J (H'.ι *ᵥ u) H'.x = 0 := fun u => (hA.orth u).1
    have hB1 : symp (R := AF F) (cA σ) (-1) (incM F X.J) (dbl (incM F W.J))
        (Matrix.fromCols 0 (Matrix.vecMulVec y₂ (incV F H'.x)) + Matrix.fromCols P P)
        (Matrix.fromCols (Matrix.vecMulVec y₁ (incV F H'.x)) 0) = 0 := by
      have e1 : Matrix.fromCols 0 (Matrix.vecMulVec y₂ (incV F H'.x)) + Matrix.fromCols P P =
          Matrix.fromCols P (Matrix.vecMulVec y₂ (incV F H'.x) + P) := by ext i j; cases j <;> simp
      rw [e1, symp, GlobalTheory.MixedWForm.hTens_dbl, GlobalTheory.MixedWForm.hTens_zero_right, hPdef,
        GlobalTheory.MixedWForm.hTens_orth σ _ _ _ _ hO]
      simp
    have hB2 : symp (R := AF F) (cA σ) (-1) (incM F X.J) (dbl (incM F W.J)) (Matrix.fromCols P P)
        (Matrix.fromCols 0 (Matrix.vecMulVec y₂ (incV F H'.x))) = 0 := by
      rw [symp, GlobalTheory.MixedWForm.hTens_dbl, GlobalTheory.MixedWForm.hTens_zero_right, hPdef, GlobalTheory.MixedWForm.hTens_orth σ _ _ _ _ hO]
      simp
    rw [hsplit, ← GlobalTheory.MixedWForm.rho_rho_of dd _ _ _ hB1, ← GlobalTheory.MixedWForm.rho_rho_of dd _ _ _ hB2]
    have hm1 : dd.rho B.ψ (Matrix.fromCols P P) Ψ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d) :=
      GlobalTheory.HeisSchA.schr_mem_schA B.ψ hstd _ Ψ hΨ
    have hm2 : dd.rho B.ψ (Matrix.fromCols 0 (Matrix.vecMulVec y₂ (incV F H'.x)))
        (dd.rho B.ψ (Matrix.fromCols P P) Ψ) ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d) :=
      GlobalTheory.HeisSchA.schr_mem_schA B.ψ hstd _ _ hm1
    rw [hlamx, hlamx, (h3 y₁ _ hm2).1, (h3 y₂ _ hm1).2]
    have hz : Matrix.fromCols P P = Matrix.fromCols Z Z * (Matrix.fromBlocks (incM F H'.ι) 0 0 (incM F H'.ι))ᵀ := by
      rw [Matrix.fromBlocks_transpose, Matrix.fromCols_mul_fromBlocks]; simp [hPdef]
    rw [hz, h2 _ _ hΨ, Darboux.rho, hdd₁ Z Z]
    exact DiagForm.lDiag_schr _ _ _ (h1 Ψ hΨ)
  obtain ⟨gd, hgd⟩ := levi_block' σ W m
  have g1 : (gd.1.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) *ᵥ Sum.elim (incV F H'.x) (0 : Fin d → AE F E) =
      t.1 • Sum.elim (incV F H'.x) (0 : Fin d → AE F E) := by
    rw [hgd, Matrix.fromBlocks_mulVec]
    ext i; cases i <;> simp [hm.1]
  have g2 : (gd.1.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) *ᵥ Sum.elim (0 : Fin d → AE F E) (incV F H'.x) =
      Sum.elim (0 : Fin d → AE F E) (incV F H'.x) := by
    rw [hgd, Matrix.fromBlocks_mulVec]
    ext i; cases i <;> simp
  have g3 : (gd.1.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) * Matrix.fromRows (incM F H'.ι) (incM F H'.ι) =
      Matrix.fromRows (incM F H'.ι) (incM F H'.ι) := by
    rw [hgd, Matrix.fromBlocks_mul_fromRows, hm.2.2]
    simp [mat]
  have hS := GlobalTheory.T.doubled_space_darboux_character F E σ B hP.base n d d₁ X W W₁ H' i₀ i₁ r' s' r₁ s₁ hP.skew hP₁.skew hA χX dd omd
    hspl.2.1.toIsSplitting hspl.2.2 lam hadm hinvL t gd g1 g2 g3
  obtain ⟨Φ, hΦ, hΦne⟩ := hne
  have hKΦ := GlobalTheory.SchAConj.star_mem_schA F _ Φ hΦ
  have hbx := GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ Φ hΦ _ hKΦ
  have hv := hS _ hbx
  rw [hbox m gd hgd Φ hΦ _ hKΦ] at hv
  rw [hlamx, hlamx] at hv
  rw [h5, h5, hk Φ hΦ] at hv
  have hc : conjLin e (fun x => star (Φ x)) = fun y => star (e Φ y) := by
    funext y; simp [conjLin_apply]
  rw [hc] at hv
  have hb : boxFun (k • e Φ) (fun y => star (e Φ y)) = k • boxFun (e Φ) (fun y => star (e Φ y)) := by
    funext x; simp only [boxFun, Pi.smul_apply, smul_eq_mul]; ring
  rw [hb, map_smul, smul_eq_mul] at hv
  have hL0 := GlobalTheory.MixedWForm.lDiag_box_star_ne (he.maps Φ hΦ) hΦne
  have hkv := mul_right_cancel₀ hL0 hv
  rw [GlobalTheory.T.adelic_modulus_norm_eq_abs F E t] at hkv

  obtain ⟨l, hl, hlinv, φ₀, hφ₀, hl0⟩ := GlobalTheory.diagLagrangian_form F B.ψ (Fin n × Fin d)
  have hinv : ∀ z : Matrix (Fin n) (Fin d) (AE F E), ∀ φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)),
      l (dd.rho B.ψ (z * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E))ᵀ) φ) = l φ := by
    intro z φ hφ
    have hzz : z * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E))ᵀ = Matrix.fromCols z z := by
      simp [diagCols, Matrix.transpose_fromRows, Matrix.mul_fromCols]
    rw [hzz, Darboux.rho, hdc z z]
    exact hlinv _ _ φ hφ
  refine ⟨l, hl, hinv, fun φ hφ => ?_, φ₀, hφ₀, hl0⟩
  obtain ⟨hT, hdet⟩ := GlobalTheory.T.seesaw_pair_restriction_is_pair F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hA hP₁ t m hm
  have hTu : IsUnit (GlobalTheory.DblUnip.diagMat (cA σ).toRingHom (incM F W.J) (incV F H'.x) (incV F H'.y)
      ((↑t⁻¹ : AE F E) - 1)).det := by
    rw [hdet]; exact (Units.map (cA σ).toMonoidHom t⁻¹).isUnit
  let T : GL (Fin d) (AE F E) := Matrix.nonsingInvUnit _ hTu
  have hsieg := hspl.2.2 l hl hinv p T (by rw [hp]; exact hT) φ hφ
  have hdetT : Matrix.GeneralLinearGroup.det T = Units.map (cA σ).toMonoidHom t⁻¹ := Units.ext (by
    simp only [Matrix.GeneralLinearGroup.val_det_apply]; exact hdet)
  rw [hdetT] at hsieg
  have hc' := GlobalTheory.T.witt_character_conjugate_inverse F E σ B n d X W M χX χW om r s r' s' hP t⁻¹
  have hmo := GlobalTheory.T.adelic_modulus_norm_eq_abs F E (Units.map (cA σ).toMonoidHom t⁻¹)
  have habs : (absE F E (Units.map (cA σ).toMonoidHom t⁻¹) : ℝ) = ((absE F E t : ℝ))⁻¹ := by
    rw [show Units.map (cA σ).toMonoidHom t⁻¹ = GlobalTheory.Doubling.conjUnit σ t⁻¹ from rfl, GlobalTheory.Doubling.absE_conjUnit, map_inv,
      NNReal.coe_inv]
  rw [hc', map_inv, inv_inv, hmo, habs, Fintype.card_fin] at hsieg
  rw [hsieg, hkv]
  have hA0 : (0 : ℝ) < (absE F E t : ℝ) := by
    have e1 : absE F E t * absE F E t⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    have e2 : absE F E t ≠ 0 := fun h => by rw [h, zero_mul] at e1; exact zero_ne_one e1
    exact_mod_cast pos_iff_ne_zero.mpr e2
  have e3 : ((absE F E t : ℝ))⁻¹ ^ ((n : ℝ) / 2) = (absE F E t : ℝ) ^ ((n : ℝ) / 2) * (absE F E t : ℝ) ^ (-(n : ℝ)) := by
    rw [Real.inv_rpow hA0.le, ← Real.rpow_neg hA0.le, ← Real.rpow_add hA0]; ring_nf
  rw [e3]; push_cast; ring

end GlobalTheory.TorusLamP

end
