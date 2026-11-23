import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneSecondVariableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneFirstVariableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEvaluationZeroConeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodSchrodingerModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharactersRestrictionEtaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairDoubleDescentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairDoubleDescentModelsStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.EvLawA

theorem resEtaPow_div' {R E : Type} [CommRing R] [CommRing E] [Algebra R E] [Invertible (2 : R)] {K : Subgroup Rˣ}
    {χ₁ χ₂ : Eˣ →* Circle} {m n : ℕ} (h₁ : ResEtaPow K χ₁ m) (h₂ : ResEtaPow K χ₂ n) :
    ResEtaPow K (χ₁ / χ₂) (m + n) := by
  intro x
  rw [MonoidHom.div_apply, Circle.coe_div, h₁ x, h₂ x]
  split_ifs
  · simp
  · have h : ((-1 : ℂ) ^ n) * (-1) ^ n = 1 := by rw [← pow_add, ← two_mul, pow_mul]; norm_num
    rw [div_eq_iff (pow_ne_zero _ (by norm_num)), pow_add, mul_assoc, h, mul_one]

theorem isHecke_div' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {χ₁ χ₂ : Chr F E}
    (h₁ : IsHecke F E χ₁) (h₂ : IsHecke F E χ₂) : IsHecke F E (χ₁ / χ₂) :=
  ⟨h₁.1.div' h₂.1, fun x => by rw [MonoidHom.div_apply, h₁.2 x, h₂.2 x]; exact div_self' 1⟩

theorem incM_one' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) :
    incM F (1 : Matrix (Fin n) (Fin n) E) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

theorem vecMulVec_mul_transpose {R : Type} [CommRing R] {k l p : ℕ} (a : Fin k → R) (b : Fin p → R)
    (M : Matrix (Fin l) (Fin p) R) : Matrix.vecMulVec a b * Mᵀ = Matrix.vecMulVec a (M *ᵥ b) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.transpose_apply, Matrix.mulVec, dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

end GlobalTheory.ThK.EvLawA

open GlobalTheory.ThK.EvLawA in

theorem GlobalTheory.ThK.evLaw_isoA : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (t : (AE F E)ˣ) (h₁ : UA σ G₁.W.J) (m : UA σ G.W.J), IsLevi H' t h₁ m → ∀ Ψ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')),
      e (om (1, m) Ψ) = ((X.β t : ℂ) * (((absE F E t : ℝ) ^ (((b + 2 : ℕ) : ℝ) / 2) : ℝ) : ℂ)) • om₁ (1, h₁) (e Ψ) := by
  intro hKP F E _ _ _ _ _ σ B b a' G G₁ H H' cfg e hev X om om' om₁ om₁' T T₁ t h₁ m hL Ψ hΨ
  have P : IsPair B G.M X.β (X.β / X.α) om (b + 2 - G.p) G.p _ _ :=
    ⟨T.base, T.geo.hV, T.geo.hW, T.geo.hM, T.chars.heckeβ, isHecke_div' T.chars.heckeβ T.chars.heckeα,
      T.chars.resβ, resEtaPow_div' T.chars.resβ T.chars.resα, T.weil⟩
  have P₁ : IsPair B G₁.M X.β (X.β / X.α) om₁ (b - G₁.p) G₁.p _ _ :=
    ⟨T₁.base, T₁.geo.hV, T₁.geo.hW, T₁.geo.hM, T₁.chars.heckeβ, isHecke_div' T₁.chars.heckeβ T₁.chars.heckeα,
      T₁.chars.resβ, resEtaPow_div' T₁.chars.resβ T₁.chars.resα, T₁.weil⟩

  obtain ⟨Ma, hMa⟩ := GlobalTheory.T.exists_good_schrodinger_model F E σ B T.base (b + 2) (b + a') G.V G₁.W _ _ _ _ T.geo.hV T₁.geo.hW
  obtain ⟨oma, hwa⟩ := GlobalTheory.T.hecke_characters_restriction_eta hKP.base F E σ B T.base (b + 2) (b + a') G.V G₁.W _ _ _ _ T.geo.hV T₁.geo.hW Ma hMa
    X.β (X.β / X.α) T.chars.heckeβ (isHecke_div' T.chars.heckeβ T.chars.heckeα) T.chars.resβ
    (resEtaPow_div' T₁.chars.resβ T₁.chars.resα)
  have Pa : IsPair B Ma X.β (X.β / X.α) oma (b + 2 - G.p) G.p _ _ :=
    ⟨T.base, T.geo.hV, T₁.geo.hW, hMa, T.chars.heckeβ, isHecke_div' T.chars.heckeβ T.chars.heckeα,
      T.chars.resβ, resEtaPow_div' T₁.chars.resβ T₁.chars.resα, hwa⟩

  obtain ⟨e₁, he₁⟩ := ((GlobalTheory.T.theta_evaluation_zero_cone hKP.base).1 F E σ B (b + 2) (b + 2 + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _ P
    (b + a') G.V G₁.W H' 0 (b + 1) Ma rfl cfg.hH' hMa).1
  obtain ⟨⟨e₂, he₂⟩, law₂⟩ := GlobalTheory.T.adapted_plane_first_variable hKP.base F E σ B (b + 2) (b + a') G.V G₁.W Ma X.β (X.β / X.α) oma _ _ _ _ Pa
    b G₁.V H 0 (b + 1) G₁.M om₁ _ _ cfg.hH P₁

  have heisC : ∀ (z : Matrix (Fin b) (Fin (b + a')) (AE F E)), ∀ Φ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')),
      (e₂ ∘ₗ e₁) (G.M.co.rho B.ψ (incM F H.ι * z * (incM F H'.ι)ᵀ) Φ) = G₁.M.co.rho B.ψ z ((e₂ ∘ₗ e₁) Φ) := by
    intro z Φ hΦ
    have h1 := he₁.Heisenberg₂ (incM F H.ι * z) Φ hΦ
    have h2 := he₂.Heisenberg₂ z (e₁ Φ) (he₁.maps Φ hΦ)
    rw [incM_one', Matrix.one_mul] at h1
    rw [incM_one', Matrix.transpose_one, Matrix.mul_one] at h2
    simp only [LinearMap.comp_apply]
    rw [h1, h2]
  have invC : ∀ u ∈ isoA H H', ∀ Φ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')),
      (e₂ ∘ₗ e₁) (G.M.co.rho B.ψ u Φ) = (e₂ ∘ₗ e₁) Φ := by
    intro u hu Φ hΦ
    simp only [LinearMap.comp_apply]
    rcases hu with hu | ⟨z, rfl⟩
    · rw [he₁.inv u hu Φ hΦ]
    · have h1 := he₁.Heisenberg₂ (Matrix.vecMulVec (incV F H.x) z) Φ hΦ
      rw [incM_one', Matrix.one_mul, vecMulVec_mul_transpose] at h1
      rw [h1, he₂.inv _ ⟨z, rfl⟩ _ (he₁.maps Φ hΦ)]
  obtain ⟨c, hc⟩ := GlobalTheory.T.pair_double_descent hKP.base F E σ B (b + 2) (b + 2 + a') b (b + a') G.V G.W G₁.V G₁.W G.M X.β (X.β / X.α) om
    _ _ _ _ P H H' 0 (b + 1) 0 (b + 1) G₁.M cfg.hH cfg.hH' T₁.geo.hM e hev (e₂ ∘ₗ e₁) heisC invC
  obtain ⟨Φ₀, hΦ₀, hne⟩ := GlobalTheory.T.pair_double_descent_models hKP.base F E σ B (b + 2) (b + 2 + a') b (b + a') G.V G.W G₁.V G₁.W G.M X.β (X.β / X.α) om
    _ _ _ _ P H H' 0 (b + 1) 0 (b + 1) Ma oma _ _ G₁.M cfg.hH cfg.hH' Pa T₁.geo.hM e₁ e₂ he₁ he₂
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hne
    have := hc Φ₀ hΦ₀
    rw [zero_smul, LinearMap.comp_apply] at this
    exact this

  have hpres : om (1, m) Ψ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')) := (T.weil.isUSplitting).pres _ _ hΨ
  have hLX : IsLevi (W₁ := G₁.V) H 1 (1 : UA σ G₁.V.J) (1 : UA σ G.V.J) := by
    refine ⟨?_, ?_, ?_⟩
    · show (1 : Matrix _ _ _) *ᵥ _ = _
      simp
    · show (1 : Matrix _ _ _) *ᵥ _ = _
      simp
    · show (1 : Matrix _ _ _) * _ = _ * (1 : Matrix _ _ _)
      simp
  have key : e₂ (e₁ (om (1, m) Ψ)) = ((X.β t : ℂ) * (((absE F E t : ℝ) ^ (((b + 2 : ℕ) : ℝ) / 2) : ℝ) : ℂ)) •
      om₁ (1, h₁) (e₂ (e₁ Ψ)) := by
    have h1 := GlobalTheory.T.adapted_plane_second_variable hKP.base F E σ B (b + 2) (b + 2 + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _ P (b + a') G₁.W H'
      0 (b + 1) Ma oma _ _ cfg.hH' Pa e₁ he₁ 1 t h₁ m hL 1 (Subgroup.one_mem _) Ψ hΨ
    have h2 := law₂ e₂ he₂ h₁ 1 1 1 hLX 1 (Subgroup.one_mem _) (e₁ Ψ) (he₁.maps Ψ hΨ)
    simp only [one_mul, map_one, Circle.coe_one, NNReal.coe_one, Real.one_rpow, Complex.ofReal_one, one_smul] at h1 h2
    rw [h1, map_smul, h2]
  calc e (om (1, m) Ψ) = c⁻¹ • (c • e (om (1, m) Ψ)) := by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
    _ = c⁻¹ • (((X.β t : ℂ) * (((absE F E t : ℝ) ^ (((b + 2 : ℕ) : ℝ) / 2) : ℝ) : ℂ)) • om₁ (1, h₁) (c • e Ψ)) := by
        rw [← hc _ hpres, ← hc _ hΨ]
        simp only [LinearMap.comp_apply]
        rw [key]
    _ = _ := by rw [map_smul, smul_comm _ c, smul_smul, inv_mul_cancel₀ hc0, one_smul]
