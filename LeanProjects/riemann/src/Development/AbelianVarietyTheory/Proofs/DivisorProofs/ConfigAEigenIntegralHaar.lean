import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CmCharacterConjugateInverse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingLeviTranslationIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingHaarEigenUnfoldingStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

theorem GlobalTheory.ThK.cone_levi_law : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ (K : Subgroup (UA σ G.V.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure →
      ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
      ∀ Φ ∈ PolData B G.M, ∀ (t : (AE F E)ˣ) (h₁ : UA σ G₁.W.J) (m : UA σ G.W.J), IsLevi H' t h₁ m → ∀ h,
        G₁.M.I om₁ (cone B G.M om e K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) (om (1, m * h) Φ)) 1 =
          (X.α t : ℂ) * (((absE F E t : ℝ) ^ ((a' : ℝ) / 2) : ℝ) : ℂ) *
            G₁.M.I om₁ (cone B G.M om e K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) (om (1, h) Φ)) h₁ := by
  intro hKP F E _ _ _ _ _ σ B b a' G G₁ H H' cfg e hev K μK μ hK hμK hμ X om om' om₁ om₁' T T₁ Φ hΦ t h₁ m hL h
  have hS : Φ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')) := by
    refine Submodule.span_le.mpr ?_ hΦ
    rintro _ ⟨f, -, φ, hφ, hv, rfl⟩
    refine GlobalTheory.TensUniq.pure_mem_schA f φ hφ ?_
    filter_upwards [hv, T.geo.hM.std] with v h1 h2
    rw [h1, h2]
  have hpres : ∀ x, ∀ Ψ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')), om x Ψ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')) :=
    fun x Ψ hΨ => (T.weil.isUSplitting).pres x Ψ hΨ
  have himpl := (T.weil.isUSplitting).impl
  have hrho : ∀ w, ∀ Ψ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')), G.M.co.rho B.ψ w Ψ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')) :=
    fun w Ψ hΨ => GlobalTheory.HeisSchA.rho_mem_schA G.M B.ψ T.base.std w Ψ hΨ
  have hcm := T.base.cm

  set z : ℕ := (b + 2 - a') / 2 with hz
  set ct : (AE F E)ˣ := Units.map (cA σ).toMonoidHom t with hct
  set Ψ0 := om (1, h) Φ with hΨ0
  have hΨ0s : Ψ0 ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')) := hpres _ _ hS

  have hνF : ∀ a : (HeckeCharacterZeroLocus.ThmBIn.AF F)ˣ, X.ν (HeckeCharacterZeroLocus.ThmBIn.idF F E a) = 1 := by
    intro a
    have e1 : (X.α (HeckeCharacterZeroLocus.ThmBIn.idF F E a) : ℂ) = _ := T.chars.resα a
    have e2 : (X.β (HeckeCharacterZeroLocus.ThmBIn.idF F E a) : ℂ) = _ := T.chars.resβ a
    have hpar : a' % 2 = (b + 2) % 2 := by
      obtain ⟨k, hk⟩ := T.geo.even
      omega
    rw [← Circle.coe_eq_one, Chars.ν, MonoidHom.div_apply, Circle.coe_div, e1, e2]
    split_ifs
    · simp
    · rw [neg_one_pow_eq_pow_mod_two (R := ℂ), hpar, ← neg_one_pow_eq_pow_mod_two (R := ℂ)]
      exact div_self (pow_ne_zero _ (by norm_num))
  have hνct : X.ν ct = (X.ν t)⁻¹ := GlobalTheory.ideleChar_conj_eq_inv_of_trivial_on_base F E σ hcm X.ν hνF t ct rfl
  have habs : absE F E ct = absE F E t := GlobalTheory.Doubling.absE_conjUnit σ t

  have hlt : a' < b + 2 := T.geo.lt
  have h2z : 2 * z + a' = b + 2 := by
    obtain ⟨k, hk⟩ := T.geo.even
    omega
  have hr : (0 : ℝ) < (absE F E t : ℝ) := by
    have h1 : absE F E t * absE F E t⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    have h2 : absE F E t ≠ 0 := left_ne_zero_of_mul_eq_one h1
    exact_mod_cast pos_iff_ne_zero.mpr h2
  have hsc : (X.β t : ℂ) * (((absE F E t : ℝ) ^ (((b + 2 : ℕ) : ℝ) / 2) : ℝ) : ℂ) =
      (X.α t : ℂ) * (((absE F E t : ℝ) ^ ((a' : ℝ) / 2) : ℝ) : ℂ) * ((X.ν ct : ℂ) * ((absE F E ct : ℝ) : ℂ) ^ z) := by
    have hexp : ((b + 2 : ℕ) : ℝ) / 2 = (a' : ℝ) / 2 + (z : ℝ) := by
      have : ((2 * z + a' : ℕ) : ℝ) = ((b + 2 : ℕ) : ℝ) := by rw [h2z]
      push_cast at this ⊢
      linarith
    rw [hνct, habs, hexp, Real.rpow_add hr, Real.rpow_natCast, Chars.ν, MonoidHom.div_apply, Circle.coe_inv, Circle.coe_div]
    have hα : (X.α t : ℂ) ≠ 0 := Circle.coe_ne_zero _
    have hβ : (X.β t : ℂ) ≠ 0 := Circle.coe_ne_zero _
    push_cast
    field_simp
  have s1 : ∀ (k : K) l, G.M.co.rho B.ψ (shiftA H H' l) (om (k.1, 1) (om (1, m * h) Φ)) =
      om (1, m) (G.M.co.rho B.ψ (shiftA H H' (l * ct)) (om (k.1, 1) Ψ0)) := by
    intro k l
    have hc : om (k.1, 1) (om (1, m * h) Φ) = om (1, m) (om (k.1, 1) Ψ0) := by
      simp only [hΨ0, ← Module.End.mul_apply, ← map_mul]
      congr 2
      ext <;> simp
    rw [hc, himpl (1, m) _ _ (hpres _ _ hΨ0s)]
    congr 1
    have hy := hL.2.1
    show l.1 • Matrix.vecMulVec (incV F H.x) (incV F H'.y) =
      (1 : Matrix (Fin (b + 2)) (Fin (b + 2)) (AE F E)) * ((l * ct).1 • Matrix.vecMulVec (incV F H.x) (incV F H'.y)) * (mat m)ᵀ
    rw [Matrix.one_mul]
    ext i j
    have hyj := congrFun hy j
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hyj
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
    have hs : ∀ k, (l * ct).1 * (incV F H.x i * incV F H'.y k) * mat m j k = ((l * ct).1 * incV F H.x i) * (mat m j k * incV F H'.y k) := fun k => by ring
    simp only [hs, ← Finset.mul_sum, hyj]
    have hu : (l * ct).1 * (cA σ) (t⁻¹).1 = l.1 := by
      rw [Units.val_mul, hct]
      show l.1 * (cA σ) t.1 * (cA σ) (t⁻¹).1 = l.1
      rw [mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one]
    rw [← hu]
    ring

  have key : cone B G.M om e K μK μ (shiftA H H') X.ν z (om (1, m * h) Φ) =
      ((X.α t : ℂ) * (((absE F E t : ℝ) ^ ((a' : ℝ) / 2) : ℝ) : ℂ)) • om₁ (1, h₁) (cone B G.M om e K μK μ (shiftA H H') X.ν z Ψ0) := by
    rw [GlobalTheory.T.doubling_haar_eigen_unfolding hKP F E σ B b a' G G₁ H H' cfg e hev K μK μ hK hμK hμ X om om' om₁ om₁' T T₁ h₁ Ψ0 hΨ0s]
    funext y
    simp only [cone, Pi.smul_apply, smul_eq_mul]
    rw [← integral_const_mul]
    congr 1
    funext k
    have : BorelSpace (AE F E)ˣ := ⟨rfl⟩
    rw [← integral_const_mul]
    conv_rhs => rw [← integral_mul_right_eq_self (μ := μ) _ ct]
    congr 1
    funext l
    rw [s1 k l, GlobalTheory.T.doubling_levi_translation_identity hKP F E σ B b a' G G₁ H H' cfg e hev X om om' om₁ om₁' T T₁ t h₁ m hL _
      (hrho _ _ (hpres _ _ hΨ0s)), Pi.smul_apply, smul_eq_mul, hsc, map_mul, map_mul,
      Circle.coe_mul, NNReal.coe_mul, Complex.ofReal_mul, mul_pow]
    ring
  have hlin : ∀ (c : ℂ) (φ : Fn F b (b + a')) (x : UA σ G₁.W.J), G₁.M.I om₁ (c • φ) x = c * G₁.M.I om₁ φ x := by
    intro c φ x
    simp only [Model.I, theta, map_smul, thetaSum, Pi.smul_apply, smul_eq_mul, tsum_mul_left]
    exact integral_const_mul _ _
  have hmove : ∀ (φ : Fn F b (b + a')), G₁.M.I om₁ (om₁ (1, h₁) φ) 1 = G₁.M.I om₁ φ h₁ := by
    intro φ
    simp only [Model.I, theta]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    show thetaSum F (om₁ (g, 1) (om₁ (1, h₁) φ)) = thetaSum F (om₁ (g, h₁) φ)
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
  rw [key, hlin, hmove]
