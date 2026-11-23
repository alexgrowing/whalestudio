import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnipotentScalarTranslationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawPairRestrictionIsPairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicModulusNormEqAbsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittCharacterConjugateInverseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawPairRestrictionLeviStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.TorusValueP

theorem levi_block {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {d : ℕ}
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

theorem torus_evalZero_value : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ → ∀ e, IsEv B M M₁ 1 H'.ι (iso0 n H') e →
      ∀ t m, IsLevi (W₁ := W₁) H' t 1 m →
        ∀ k : ℂ, (∀ Φ ∈ schA F (Fin n × Fin d), e (om (1, m) Φ) = k • e Φ) → (∃ Φ ∈ schA F (Fin n × Fin d), e Φ ≠ 0) →
        k = (χX t : ℂ) * (((absE F E t : ℝ) ^ ((n : ℝ) / 2) : ℝ) : ℂ) := by
  intro hPr F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hA hP₁ e he t m hm k hk hne
  obtain ⟨⟨_, dd, omd, hdc, hspl, hbox⟩, -, -⟩ := hP.weil
  obtain ⟨u, hu⟩ := GlobalTheory.T.doubled_unipotent_scalar_translation F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ hA ((↑t⁻¹ : AE F E) - 1)
  obtain ⟨gd, hgd⟩ := levi_block σ W m
  obtain ⟨hT, hdet⟩ := GlobalTheory.T.seesaw_pair_restriction_is_pair F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hA hP₁ t m hm
  have hp : ((gd * u).1.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) =
      Matrix.fromBlocks (mat m) 0 0 1 * GlobalTheory.DblUnip.unipMat (cA σ).toRingHom (incM F W.J) (incV F H'.x) (incV F H'.y)
        ((↑t⁻¹ : AE F E) - 1) := by
    rw [← hgd, ← hu]; rfl
  obtain ⟨Λ, hadm, hinv, hΛp, φ₀, hφ₀, hne0⟩ := GlobalTheory.T.seesaw_pair_restriction_levi hPr F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁
    r₁ s₁ hA hP₁ e he t m hm k hk hne dd omd hdc hspl (fun g gd h φ₁ h₁ φ₂ h₂ => hbox g gd h φ₁ h₁ φ₂ h₂) (gd * u) hp
  have hTu : IsUnit (GlobalTheory.DblUnip.diagMat (cA σ).toRingHom (incM F W.J) (incV F H'.x) (incV F H'.y)
      ((↑t⁻¹ : AE F E) - 1)).det := by
    rw [hdet]; exact (Units.map (cA σ).toMonoidHom t⁻¹).isUnit
  let T : GL (Fin d) (AE F E) := Matrix.nonsingInvUnit _ hTu
  have hsieg := hspl.2.2 Λ hadm hinv (gd * u) T (by rw [hp]; exact hT) φ₀ hφ₀
  have hdetT : Matrix.GeneralLinearGroup.det T = Units.map (cA σ).toMonoidHom t⁻¹ := Units.ext (by
    simp only [Matrix.GeneralLinearGroup.val_det_apply]; exact hdet)
  rw [hdetT, hΛp φ₀ hφ₀] at hsieg
  have hc := GlobalTheory.T.witt_character_conjugate_inverse F E σ B n d X W M χX χW om r s r' s' hP t⁻¹
  have hmo := GlobalTheory.T.adelic_modulus_norm_eq_abs F E (Units.map (cA σ).toMonoidHom t⁻¹)
  have habs : (absE F E (Units.map (cA σ).toMonoidHom t⁻¹) : ℝ) = ((absE F E t : ℝ))⁻¹ := by
    rw [show Units.map (cA σ).toMonoidHom t⁻¹ = GlobalTheory.Doubling.conjUnit σ t⁻¹ from rfl, GlobalTheory.Doubling.absE_conjUnit, map_inv,
      NNReal.coe_inv]
  rw [hc, map_inv, inv_inv, hmo, habs, Fintype.card_fin] at hsieg
  have hA0 : (0 : ℝ) < (absE F E t : ℝ) := by
    have h1 : absE F E t * absE F E t⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    have h2 : absE F E t ≠ 0 := fun h => by rw [h, zero_mul] at h1; exact zero_ne_one h1
    exact_mod_cast pos_iff_ne_zero.mpr h2
  have h := mul_right_cancel₀ hne0 hsieg
  have e1 : ((absE F E t : ℝ))⁻¹ ^ ((n : ℝ) / 2) * (absE F E t : ℝ) ^ (n : ℝ) = (absE F E t : ℝ) ^ ((n : ℝ) / 2) := by
    rw [Real.inv_rpow hA0.le, ← Real.rpow_neg hA0.le, ← Real.rpow_add hA0]; ring_nf
  have e2 : (absE F E t : ℝ) ^ (-(n : ℝ)) * (absE F E t : ℝ) ^ (n : ℝ) = 1 := by
    rw [← Real.rpow_add hA0]; simp
  calc k = k * ((((absE F E t : ℝ) ^ (-(n : ℝ)) * (absE F E t : ℝ) ^ (n : ℝ) : ℝ)) : ℂ) := by rw [e2]; simp
    _ = (k * ((((absE F E t : ℝ) ^ (-(n : ℝ)) : ℝ)) : ℂ)) * ((((absE F E t : ℝ) ^ (n : ℝ) : ℝ)) : ℂ) := by push_cast; ring
    _ = (χX t : ℂ) * (((((absE F E t : ℝ))⁻¹ ^ ((n : ℝ) / 2) : ℝ)) : ℂ) * ((((absE F E t : ℝ) ^ (n : ℝ) : ℝ)) : ℂ) := by rw [h]
    _ = (χX t : ℂ) * (((((absE F E t : ℝ))⁻¹ ^ ((n : ℝ) / 2) * (absE F E t : ℝ) ^ (n : ℝ) : ℝ)) : ℂ) := by push_cast; ring
    _ = _ := by rw [e1]

end GlobalTheory.TorusValueP
