import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialFockSpaceStableArchimedeanMaximalCompa

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.KInfFockDeg

open GlobalTheory.RealLift GlobalTheory.KInfPol

theorem fockDeg_stable_kInf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (om : Rep σ X W) (χ₁ χ₂ : Chr F E) (r s r' s' : ℕ),
    B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ → M.IsWeil B.ψ χ₁ χ₂ om →
    ∀ k ∈ KInf σ W B.emb, ∀ j : ℕ, ∀ f ∈ fockDeg M B.ψ B.emb j, ∀ f₁ : SInf F (Fin n × Fin d),
      Acts (evI F) (om (1, k)) (⇑f) (⇑f₁) → f₁ ∈ fockDeg M B.ψ B.emb j := by
  intro F E _ _ _ _ _ σ B n d X W M om χ₁ χ₂ r s r' s' hB _ _ hM hw k hk j f hf f₁ hf₁
  obtain ⟨A, hA⟩ := GlobalTheory.T.exists_archOperator_compact_unitaryW F E σ B n d X W M om χ₁ χ₂ hB hM hw k hk
  obtain ⟨D, hD⟩ := GlobalTheory.T.archHeisenbergDerivatives_exist F E σ _ _ _ B.ψ _ _ M.co hB.std
  have hL := actsLaws F (Fin n × Fin d)
  have hSD : ∀ u, At (evI F) u → ∀ φ, SD (M.heisLine B.ψ u) φ (D u φ) := fun u hu φ => (hD u hu φ).1
  have hAD : ∀ u, At (evI F) u → ∀ φ : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine B.ψ u) φ (D u φ) :=
    fun u hu φ => (hL φ _ φ).1 _ (heisLine_zero M B.ψ u) (hSD u hu φ)
  have hint : ∀ u, At (evI F) u → ∀ φ : SInf F (Fin n × Fin d),
      ActsD (evI F) (M.heisLine B.ψ (u * (mat k)ᵀ)) (A φ) (A (D u φ)) :=
    fun u hu φ => (hL _ _ φ).1 _ (heisLine_zero M B.ψ _) (sd_intertwine hw k (hA φ) (hA _) (hSD u hu φ))
  have hkk : (mat k⁻¹)ᵀ * (mat k)ᵀ = 1 := by
    rw [← Matrix.transpose_mul]
    change (mat (k * k⁻¹))ᵀ = 1
    rw [mul_inv_cancel]
    exact Matrix.transpose_one
  have hcan : ∀ u : Matrix (Fin n) (Fin d) (AE F E), u * (mat k⁻¹)ᵀ * (mat k)ᵀ = u := fun u => by
    rw [Matrix.mul_assoc, hkk, Matrix.mul_one]
  have hvac : ∀ f₀, M.IsGauss B.ψ B.emb f₀ → M.IsGauss B.ψ B.emb (A f₀) := by
    intro f₀ hf₀
    obtain ⟨ε, hε⟩ := hf₀
    refine ⟨ε, fun u u' hu hu' huu g g' hg hg' => ?_⟩
    have hv := at_mul_right hu (mat k⁻¹)ᵀ
    have hv' := at_mul_right hu' (mat k⁻¹)ᵀ
    have h1 := hint _ hv f₀
    have h2 := hint _ hv' f₀
    rw [hcan] at h1 h2
    have e1 := (hL _ _ _).2.2.1 _ hg h1
    have e2 := (hL _ _ _).2.2.1 _ hg' h2
    have key := hε _ _ hv hv' (fun w => ?_) _ _ (hAD _ hv f₀) (hAD _ hv' f₀)
    · rw [e1, e2, key, map_smul]
    · have hm : (mat k⁻¹).map (piInf (B.emb w)) * (mat k).map (piInf (B.emb w)) = 1 := by
        rw [← Matrix.map_mul]
        change (mat (k⁻¹ * k)).map _ = 1
        rw [inv_mul_cancel]
        exact Matrix.map_one _ (map_zero _) (map_one _)
      have hm' : (mat k).map (piInf (B.emb w)) * (mat k⁻¹).map (piInf (B.emb w)) = 1 := mul_eq_one_comm.1 hm
      have hc : (mat k⁻¹).map (piInf (B.emb w)) * W.θ w = W.θ w * (mat k⁻¹).map (piInf (B.emb w)) := by
        calc _ = (mat k⁻¹).map (piInf (B.emb w)) * W.θ w *
              ((mat k).map (piInf (B.emb w)) * (mat k⁻¹).map (piInf (B.emb w))) := by rw [hm', Matrix.mul_one]
          _ = (mat k⁻¹).map (piInf (B.emb w)) * (W.θ w * (mat k).map (piInf (B.emb w))) *
              (mat k⁻¹).map (piInf (B.emb w)) := by simp only [Matrix.mul_assoc]
          _ = _ := by rw [← (hk.2 w).eq, ← Matrix.mul_assoc, hm, Matrix.one_mul]
      rw [Matrix.map_mul, Matrix.map_mul, huu w, Matrix.transpose_map, Matrix.smul_mul]
      congr 1
      simp only [Matrix.mul_assoc]
      rw [← Matrix.transpose_mul, ← Matrix.transpose_mul, hc]
  have hle : ∀ i, fockDeg M B.ψ B.emb i ≤ (fockDeg M B.ψ B.emb i).comap A := by
    intro i
    induction i with
    | zero =>
      rw [fockDeg_zero]
      exact Submodule.span_le.2 fun f₀ hf₀ => Submodule.mem_comap.2 (Submodule.subset_span (hvac f₀ hf₀))
    | succ i ih =>
      rw [fockDeg_succ]
      refine sup_le (ih.trans (Submodule.comap_mono le_sup_left)) (Submodule.span_le.2 ?_)
      rintro φ₁ ⟨u, hu, φ, hφ, hφ₁⟩
      have e : φ₁ = D u φ := (hL _ _ _).2.2.1 _ hφ₁ (hAD u hu φ)
      rw [e]
      exact Submodule.mem_comap.2 (Submodule.mem_sup_right
        (Submodule.subset_span ⟨u * (mat k)ᵀ, at_mul_right hu _, A φ, ih hφ, hint u hu φ⟩))
  rw [(hL f f₁ (A f)).2.2.2.1 _ hf₁ (hA f)]
  exact hle j hf

end GlobalTheory.KInfFockDeg

end
