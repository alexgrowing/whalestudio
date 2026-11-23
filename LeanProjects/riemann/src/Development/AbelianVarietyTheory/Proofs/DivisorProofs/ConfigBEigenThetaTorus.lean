import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneSecondVariableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.LeviEvalZero

open GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem resEtaPow_div {R E : Type} [CommRing R] [CommRing E] [Algebra R E] [Invertible (2 : R)] {K : Subgroup Rˣ}
    {χ₁ χ₂ : Eˣ →* Circle} {m n : ℕ} (h₁ : ResEtaPow K χ₁ m) (h₂ : ResEtaPow K χ₂ n) :
    ResEtaPow K (χ₁ / χ₂) (m + n) := by
  intro x
  rw [MonoidHom.div_apply, Circle.coe_div, h₁ x, h₂ x]
  split_ifs
  · simp
  · have h : ((-1 : ℂ) ^ n) * (-1) ^ n = 1 := by rw [← pow_add, ← two_mul, pow_mul]; norm_num
    rw [div_eq_iff (pow_ne_zero _ (by norm_num)), pow_add, mul_assoc, h, mul_one]

theorem isHecke_div {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {χ₁ χ₂ : Chr F E}
    (h₁ : IsHecke F E χ₁) (h₂ : IsHecke F E χ₂) : IsHecke F E (χ₁ / χ₂) :=
  ⟨h₁.1.div' h₂.1, fun x => by rw [MonoidHom.div_apply, h₁.2 x, h₂.2 x]; exact div_self' 1⟩

theorem thetaSum_smul {F : Type} [Field F] [NumberField F] {κ : Type} (c : ℂ) (Φ : (κ → AF F) → ℂ) :
    thetaSum F (c • Φ) = c * thetaSum F Φ := by
  simp only [thetaSum, Pi.smul_apply, smul_eq_mul, tsum_mul_left]

end GlobalTheory.LeviEvalZero

open GlobalTheory.LeviEvalZero in

theorem GlobalTheory.ThK.evalZero_levi : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' → ∀ e, IsEv B G.M G₁.M 1 H'.ι (iso0 a H') e → ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' → ∀ Φ ∈ PolData B G.M, ∀ (t : (AE F E)ˣ) (h₁ : UA σ G₁.W.J) (m : UA σ G.W.J), IsLevi H' t h₁ m → ∀ h, G₁.M.I om₁ (e (om (1, m * h) Φ)) 1 = (X.β t : ℂ) * (((absE F E t : ℝ) ^ ((a : ℝ) / 2) : ℝ) : ℂ) * G₁.M.I om₁ (e (om (1, h) Φ)) h₁ := by
  intro hKP F E _ _ _ _ _ σ B a b G G₁ H H' cfg e hev X om om' om₁ om₁' T T₁ Φ hΦ t h₁ m hL h
  obtain ⟨p₁, q₁, V₁, V₁', W₁, M₁, M₁'⟩ := G₁
  have eV : V₁ = G.V := cfg.eV
  subst eV
  have ep : p₁ = G.p := cfg.ep
  subst ep

  have hS : ∀ Ψ ∈ PolData B G.M, Ψ ∈ schA F (Fin a × Fin (a + (b + 2))) := by
    intro Ψ hΨ
    refine Submodule.span_le.mpr ?_ hΨ
    rintro _ ⟨f, -, φ, hφ, hv, rfl⟩
    refine GlobalTheory.TensUniq.pure_mem_schA f φ hφ ?_
    filter_upwards [hv, T.geo.hM.std] with v h1 h2
    rw [h1, h2]
  have P : IsPair B G.M X.β (X.β / X.α) om (a - G.p) G.p _ _ :=
    ⟨T.base, T.geo.hV, T.geo.hW, T.geo.hM, T.chars.heckeβ, isHecke_div T.chars.heckeβ T.chars.heckeα,
      T.chars.resβ, resEtaPow_div T.chars.resβ T.chars.resα, T.weil⟩
  have P₁ : IsPair B M₁ X.β (X.β / X.α) om₁ (a - G.p) G.p _ _ :=
    ⟨T₁.base, T₁.geo.hV, T₁.geo.hW, T₁.geo.hM, T₁.chars.heckeβ, isHecke_div T₁.chars.heckeβ T₁.chars.heckeα,
      T₁.chars.resβ, resEtaPow_div T₁.chars.resβ T₁.chars.resα, T₁.weil⟩
  have hpres : ∀ x, ∀ Ψ ∈ schA F (Fin a × Fin (a + (b + 2))), om x Ψ ∈ schA F (Fin a × Fin (a + (b + 2))) :=
    fun x Ψ hΨ => (T.weil.isUSplitting).pres x Ψ hΨ
  have key := GlobalTheory.T.adapted_plane_second_variable hKP.base F E σ B a (a + (b + 2)) G.V G.W G.M X.β (X.β / X.α) om _ _ _ _ P (a + b) W₁ H' a
    (a + b + 1) M₁ om₁ _ _ cfg.hH' P₁ e hev 1 t h₁ m hL 1 (Subgroup.one_mem _) (om (1, h) Φ) (hpres _ _ (hS Φ hΦ))
  have hmul : om (1, m * h) Φ = om (1, 1 * m) (om (1, h) Φ) := by
    rw [one_mul, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]
  rw [hmul, key]
  simp only [Model.I, theta, map_smul, thetaSum_smul]
  rw [integral_const_mul]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  show thetaSum F (om₁ (g, 1) (om₁ (1, h₁) _)) = thetaSum F (om₁ (g, h₁) _)
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
