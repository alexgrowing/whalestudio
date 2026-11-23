import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CmCharacterConjugateInverse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEvaluationConfigBTripleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBLeviTriplePairStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ConeVIntegrand

theorem xTerm_levi : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' → ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' → ∀ (V₂ : Spc F E a) (n₁ : ℕ) (X₁ : Spc F E n₁) (H₀ : Plane E a n₁) (j₀ j₁ : ℕ) (M₂ : Model σ X₁ G₁.W) (e₂ : Fn F a (a + (b + 2)) →ₗ[ℂ] Fn F n₁ (a + b)), (reS G.V V₂).IsHerm σ B (a - G.p) G.p → H₀.IsAdapted σ B (reS G.V V₂) X₁ j₀ j₁ → M₂.IsGood B.ψ → IsEv B G.M M₂ H₀.ι H'.ι (isoA H₀ H') e₂ → ∀ (t : (AE F E)ˣ) (m : UA σ G.W.J), IsLevi (W₁ := G₁.W) H' t 1 m → ∀ m₀ : UA σ G.V.J, IsLevi (W₁ := X₁) H₀ (Units.map (cA σ : AE F E →* AE F E) t) 1 m₀ → ∀ Φ ∈ PolData B G.M, ∀ h g, thetaSum F (e₂ (G.M.co.rho B.ψ (shiftA H₀ H' 1) (om (g, m * h) Φ))) = (X.α t : ℂ) * (((absE F E t : ℝ) ^ (((b + 2 : ℕ) : ℝ) / 2) : ℝ) : ℂ) * (((absE F E t : ℝ) ^ ((a : ℝ) - 1) : ℝ) : ℂ) * thetaSum F (e₂ (G.M.co.rho B.ψ (shiftA H₀ H' 1) (om (m₀⁻¹ * g, h) Φ))) := by
  intro hKP F E _ _ _ _ _ σ B a b G G₁ H H' cfg X om om' om₁ om₁' T T₁ V₂ n₁ X₁ H₀ j₀ j₁ M₂ e₂ hV₂ hH₀ hM₂ hev t m hL m₀ hL₀ Φ hΦ h g
  have hS : Φ ∈ schA F (Fin a × Fin (a + (b + 2))) := by
    refine Submodule.span_le.mpr ?_ hΦ
    rintro _ ⟨f, -, φ, hφ, hv, rfl⟩
    refine GlobalTheory.TensUniq.pure_mem_schA f φ hφ ?_
    filter_upwards [hv, T.geo.hM.std] with v h1 h2
    rw [h1, h2]
  have hpres : ∀ x, ∀ Ψ ∈ schA F (Fin a × Fin (a + (b + 2))), om x Ψ ∈ schA F (Fin a × Fin (a + (b + 2))) :=
    fun x Ψ hΨ => (T.weil.isUSplitting).pres x Ψ hΨ
  have himpl := (T.weil.isUSplitting).impl
  have hrho : ∀ w, ∀ Ψ ∈ schA F (Fin a × Fin (a + (b + 2))), G.M.co.rho B.ψ w Ψ ∈ schA F (Fin a × Fin (a + (b + 2))) :=
    fun w Ψ hΨ => GlobalTheory.HeisSchA.rho_mem_schA G.M B.ψ T.base.std w Ψ hΨ
  have hcm := T.base.cm
  set ct : (AE F E)ˣ := Units.map (cA σ : AE F E →* AE F E) t with hct
  set Ψ₁ := om (m₀⁻¹ * g, h) Φ with hΨ₁
  have hΨ₁s : Ψ₁ ∈ schA F (Fin a × Fin (a + (b + 2))) := hpres _ _ hS
  set Ψ := G.M.co.rho B.ψ (shiftA H₀ H' 1) Ψ₁ with hΨ
  have hΨs : Ψ ∈ schA F (Fin a × Fin (a + (b + 2))) := hrho _ _ hΨ₁s

  have s1 : G.M.co.rho B.ψ (shiftA H₀ H' 1) (om (g, m * h) Φ) =
      om (1, m) (G.M.co.rho B.ψ (shiftA H₀ H' ct) (om (g, h) Φ)) := by
    have hc : om (g, m * h) Φ = om (1, m) (om (g, h) Φ) := by
      rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]
    rw [hc, himpl (1, m) _ _ (hpres _ _ hS)]
    congr 1
    have hy := hL.2.1
    show (1 : (AE F E)ˣ).1 • Matrix.vecMulVec (incV F H₀.x) (incV F H'.y) =
      (1 : Matrix (Fin a) (Fin a) (AE F E)) * (ct.1 • Matrix.vecMulVec (incV F H₀.x) (incV F H'.y)) * (mat m)ᵀ
    rw [Matrix.one_mul]
    ext i j
    have hyj := congrFun hy j
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hyj
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
    have hs : ∀ k, ct.1 * (incV F H₀.x i * incV F H'.y k) * mat m j k = (ct.1 * incV F H₀.x i) * (mat m j k * incV F H'.y k) :=
      fun k => by ring
    simp only [hs, ← Finset.mul_sum, hyj]
    have hu : ct.1 * (cA σ) (t⁻¹).1 = 1 := by
      rw [hct]
      show (cA σ) t.1 * (cA σ) (t⁻¹).1 = 1
      rw [← map_mul, Units.mul_inv, map_one]
    rw [Units.val_one, one_mul]
    calc incV F H₀.x i * incV F H'.y j = (ct.1 * (cA σ) (t⁻¹).1) * (incV F H₀.x i * incV F H'.y j) := by rw [hu, one_mul]
      _ = _ := by ring

  have s2 : G.M.co.rho B.ψ (shiftA H₀ H' ct) (om (g, h) Φ) = om (m₀, 1) Ψ := by
    have hc : om (g, h) Φ = om (m₀, 1) Ψ₁ := by
      rw [hΨ₁, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_inv_cancel_left, one_mul]
    rw [hc, hΨ, himpl (m₀, 1) _ _ hΨ₁s]
    congr 1
    have hx := hL₀.1
    show ct.1 • Matrix.vecMulVec (incV F H₀.x) (incV F H'.y) =
      mat m₀ * ((1 : (AE F E)ˣ).1 • Matrix.vecMulVec (incV F H₀.x) (incV F H'.y)) * (1 : Matrix (Fin (a + (b + 2))) (Fin (a + (b + 2))) (AE F E))ᵀ
    rw [Matrix.transpose_one, Matrix.mul_one, Units.val_one, one_smul]
    ext i j
    have hxi := congrFun hx i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hxi
    simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
    simp only [← mul_assoc]
    rw [← Finset.sum_mul, hxi]

  have hΨ' : om (m₀, 1) Ψ ∈ schA F (Fin a × Fin (a + (b + 2))) := hpres _ _ hΨs
  have s3 : e₂ (om (1, m) (om (m₀, 1) Ψ)) =
      (((X.β t : ℂ) * (((absE F E t : ℝ) ^ ((a : ℝ) / 2) : ℝ) : ℂ)) *
        (((X.β / X.α) ct : ℂ) * (((absE F E ct : ℝ) ^ (((a + b : ℕ) : ℝ) / 2) : ℝ) : ℂ))) • e₂ Ψ := by
    rw [GlobalTheory.T.levi_evaluation_config_b_triple hKP F E σ B a b G G₁ H H' cfg X om om' om₁ om₁' T T₁ V₂ n₁ X₁ H₀ j₀ j₁ M₂ e₂ hV₂ hH₀ hM₂ hev t m hL _ hΨ',
      GlobalTheory.T.config_b_levi_triple_pair hKP F E σ B a b G G₁ H H' cfg X om om' om₁ om₁' T T₁ V₂ n₁ X₁ H₀ j₀ j₁ M₂ e₂ hV₂ hH₀ hM₂ hev ct m₀ hL₀ _ hΨs,
      smul_smul]

  have hνF : ∀ u : (HeckeCharacterZeroLocus.ThmBIn.AF F)ˣ, X.ν (HeckeCharacterZeroLocus.ThmBIn.idF F E u) = 1 := by
    intro u
    have e1 : (X.α (HeckeCharacterZeroLocus.ThmBIn.idF F E u) : ℂ) = _ := T.chars.resα u
    have e2 : (X.β (HeckeCharacterZeroLocus.ThmBIn.idF F E u) : ℂ) = _ := T.chars.resβ u
    have hpar : (b + 2) % 2 = a % 2 := by
      obtain ⟨k, hk⟩ := T.geo.even
      omega
    rw [← Circle.coe_eq_one, Chars.ν, MonoidHom.div_apply, Circle.coe_div, e1, e2]
    split_ifs
    · simp
    · rw [neg_one_pow_eq_pow_mod_two (R := ℂ), hpar, ← neg_one_pow_eq_pow_mod_two (R := ℂ)]
      exact div_self (pow_ne_zero _ (by norm_num))
  have hνct : X.ν ct = (X.ν t)⁻¹ := GlobalTheory.ideleChar_conj_eq_inv_of_trivial_on_base F E σ hcm X.ν hνF t ct rfl
  have habs : absE F E ct = absE F E t := GlobalTheory.Doubling.absE_conjUnit σ t
  have hr : (0 : ℝ) < (absE F E t : ℝ) := by
    have h1 : absE F E t * absE F E t⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    have h2 : absE F E t ≠ 0 := left_ne_zero_of_mul_eq_one h1
    exact_mod_cast pos_iff_ne_zero.mpr h2
  have hsc : ((X.β t : ℂ) * (((absE F E t : ℝ) ^ ((a : ℝ) / 2) : ℝ) : ℂ)) *
        (((X.β / X.α) ct : ℂ) * (((absE F E ct : ℝ) ^ (((a + b : ℕ) : ℝ) / 2) : ℝ) : ℂ)) =
      (X.α t : ℂ) * (((absE F E t : ℝ) ^ (((b + 2 : ℕ) : ℝ) / 2) : ℝ) : ℂ) * (((absE F E t : ℝ) ^ ((a : ℝ) - 1) : ℝ) : ℂ) := by
    have hβα : ((X.β / X.α) ct : ℂ) = (X.α t : ℂ) / (X.β t : ℂ) := by
      have h1 : ((X.β / X.α) ct : ℂ) = ((X.ν ct)⁻¹ : Circle) := by
        rw [Chars.ν, MonoidHom.div_apply, MonoidHom.div_apply, Circle.coe_inv, Circle.coe_div, Circle.coe_div, inv_div]
      rw [h1, hνct, inv_inv, Chars.ν, MonoidHom.div_apply, Circle.coe_div]
    have hexp : (a : ℝ) / 2 + ((a + b : ℕ) : ℝ) / 2 = ((b + 2 : ℕ) : ℝ) / 2 + ((a : ℝ) - 1) := by
      push_cast; ring
    have hβ : (X.β t : ℂ) ≠ 0 := Circle.coe_ne_zero _
    rw [hβα, habs]
    calc (X.β t : ℂ) * (((absE F E t : ℝ) ^ ((a : ℝ) / 2) : ℝ) : ℂ) * ((X.α t : ℂ) / (X.β t : ℂ) * (((absE F E t : ℝ) ^ (((a + b : ℕ) : ℝ) / 2) : ℝ) : ℂ))
        = (X.α t : ℂ) * ((((absE F E t : ℝ) ^ ((a : ℝ) / 2) * (absE F E t : ℝ) ^ (((a + b : ℕ) : ℝ) / 2) : ℝ) : ℂ)) := by
          push_cast; field_simp
      _ = (X.α t : ℂ) * ((((absE F E t : ℝ) ^ (((b + 2 : ℕ) : ℝ) / 2) * (absE F E t : ℝ) ^ ((a : ℝ) - 1) : ℝ) : ℂ)) := by
          rw [← Real.rpow_add hr, ← Real.rpow_add hr, hexp]
      _ = _ := by push_cast; ring
  rw [s1, s2, s3, hsc]
  simp only [thetaSum, Pi.smul_apply, smul_eq_mul, tsum_mul_left]

end GlobalTheory.ConeVIntegrand
