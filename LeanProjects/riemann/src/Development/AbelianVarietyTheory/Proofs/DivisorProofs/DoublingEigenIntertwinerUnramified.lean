import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneSecondVariableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneFirstVariableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEvaluationZeroConeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsModelPairOfTriplesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawIdentityConfigAEigenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftInvariantRational

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.XTermLaw

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem isHecke_div {χ χ' : Chr F E} (h : IsHecke F E χ) (h' : IsHecke F E χ') : IsHecke F E (χ / χ') := by
  refine ⟨?_, fun x => ?_⟩
  · show Continuous fun x => (χ / χ') x
    simp only [MonoidHom.div_apply]
    exact h.1.div' h'.1
  · rw [MonoidHom.div_apply, h.2 x, h'.2 x, div_one]

theorem resEtaPow_div {K : Subgroup (AF F)ˣ} {χ χ' : Chr F E} {n n' : ℕ} (h : ResEtaPow K χ n)
    (h' : ResEtaPow K χ' n') : ResEtaPow K (χ / χ') (n + n') := by
  intro a
  rw [MonoidHom.div_apply, Circle.coe_div, h a, h' a]
  split_ifs
  · simp
  · rw [pow_add, div_eq_mul_inv, ← inv_pow, inv_neg, inv_one]

variable {σ : E →ₐ[F] E}

theorem isPair_of_isTriple {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W}
    {om' : Rep σ G.V' G.W} (h : IsTriple B G X om om') :
    IsPair B G.M X.β (X.β / X.α) om (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) :=
  ⟨h.base, h.geo.hV, h.geo.hW, h.geo.hM, h.chars.heckeβ, isHecke_div h.chars.heckeβ h.chars.heckeα, h.chars.resβ,
    resEtaPow_div h.chars.resβ h.chars.resα, h.weil⟩

theorem thetaSum_smul {κ : Type} (a : ℂ) (f : (κ → AF F) → ℂ) : thetaSum F (a • f) = a * thetaSum F f := by
  unfold thetaSum
  simp only [Pi.smul_apply, smul_eq_mul]
  exact tsum_mul_left

theorem mul_vecMulVec {R : Type} [CommRing R] {m n p : Type} [Fintype n] (M : Matrix m n R) (u : n → R) (v : p → R) :
    M * Matrix.vecMulVec u v = Matrix.vecMulVec (M *ᵥ u) v := by
  ext i j
  simp [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, Finset.sum_mul, mul_assoc]

theorem law : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ Φ ∈ PolData B G.M, ∀ h, ∀ (l : (AE F E)ˣ) (g₀ : UA σ G₁.V.J) (m : UA σ G.V.J), IsLevi H l g₀ m → ∀ k : UA σ G.V.J,
      thetaSum F (e (G.M.co.rho B.ψ (shiftA H H' 1) (om (m * k, h) Φ))) =
        (X.ν l : ℂ)⁻¹ * (((absE F E l : ℝ) ^ (((b + a' : ℕ) : ℝ) / 2) : ℝ) : ℂ) *
          thetaSum F (om₁ (g₀, 1) (e (G.M.co.rho B.ψ (shiftA H H' l⁻¹) (om (k, h) Φ)))) := by
  intro hK F E _ _ _ _ _ σ B b a' G G₁ H H' hC e he X om om' om₁ om₁' hT hT₁ Φ hΦ h l g₀ m hm k
  have hS := IsUWeilPair.isUSplitting hT.weil
  have hΦs : Φ ∈ schA F _ := GlobalTheory.ThK.LeftInvV.polData_le_schA hT.geo.hM hΦ
  have hΨ₀ : om (k, h) Φ ∈ schA F _ := hS.pres _ _ hΦs
  have hΨ : G.M.co.rho B.ψ (shiftA H H' l⁻¹) (om (k, h) Φ) ∈ schA F _ :=
    GlobalTheory.HeisSchA.rho_mem_schA G.M B.ψ hT.base.std _ _ hΨ₀
  have hact : actAB (cA σ) ((m, 1) : UA σ G.V.J × UA σ G.W.J) (shiftA H H' l⁻¹) = shiftA H H' 1 := by
    have hx : ((m : GL (Fin (b + 2)) (AE F E)) : Matrix (Fin (b + 2)) (Fin (b + 2)) (AE F E)) *ᵥ incV F H.x = l.1 • incV F H.x := hm.1
    simp only [actAB, shiftA]
    have h1 : (((1 : UA σ G.W.J) : GL (Fin (b + 2 + a')) (AE F E)) : Matrix (Fin (b + 2 + a')) (Fin (b + 2 + a')) (AE F E)) = 1 := rfl
    rw [h1, Matrix.transpose_one, Matrix.mul_one, Matrix.mul_smul]
    rw [mul_vecMulVec, hx, Matrix.smul_vecMulVec, smul_smul, Units.inv_mul, Units.val_one]
  have hconj : om (m, 1) (G.M.co.rho B.ψ (shiftA H H' l⁻¹) (om (k, h) Φ)) =
      G.M.co.rho B.ψ (shiftA H H' 1) (om (m * k, h) Φ) := by
    rw [hS.impl (m, 1) _ _ hΨ₀, hact, ← Module.End.mul_apply, ← map_mul]
    congr 2
    ext <;> simp
  have hP := isPair_of_isTriple hT
  have hP₁ := isPair_of_isTriple hT₁
  obtain ⟨M₂, om₂, hP₂⟩ := GlobalTheory.T.exists_model_pair_of_triples hK F E σ B b a' G G₁ X om om' om₁ om₁' hT hT₁
  obtain ⟨e₁, he₁⟩ := ((GlobalTheory.T.theta_evaluation_zero_cone hK.base).1 F E σ B (b + 2) (b + 2 + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _ hP
    (b + a') G.V G₁.W H' 0 (b + 1) M₂ rfl hC.hH' hP₂.good).1
  obtain ⟨e₂, he₂⟩ := (GlobalTheory.T.adapted_plane_first_variable hK.base F E σ B (b + 2) (b + a') G.V G₁.W M₂ X.β (X.β / X.α) om₂ _ _ _ _ hP₂ b G₁.V H 0 (b + 1)
    G₁.M om₁ _ _ hC.hH hP₁).1
  obtain ⟨c, hc, hce⟩ := GlobalTheory.T.seesaw_identity_config_a_eigen hK F E σ B b a' G G₁ H H' hC e he X om om' om₁ om₁' hT hT₁ M₂ om₂ hP₂ e₁ e₂ he₁ he₂
  have hl1 : IsLevi (W₁ := G₁.W) H' (1 : (AE F E)ˣ) (1 : UA σ G₁.W.J) (1 : UA σ G.W.J) := by
    refine ⟨?_, ?_, ?_⟩
    · change (1 : Matrix _ _ _) *ᵥ _ = _
      simp
    · change (1 : Matrix _ _ _) *ᵥ _ = _
      simp
    · change (1 : Matrix _ _ _) * _ = _ * (1 : Matrix _ _ _)
      simp
  have h₁ := GlobalTheory.T.adapted_plane_second_variable hK.base F E σ B (b + 2) (b + 2 + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _ hP (b + a') G₁.W H' 0 (b + 1)
    M₂ om₂ _ _ hC.hH' hP₂ e₁ he₁ m 1 1 1 hl1 1 (Subgroup.one_mem _) _ hΨ
  have h₂ := (GlobalTheory.T.adapted_plane_first_variable hK.base F E σ B (b + 2) (b + a') G.V G₁.W M₂ X.β (X.β / X.α) om₂ _ _ _ _ hP₂ b G₁.V H 0 (b + 1)
    G₁.M om₁ _ _ hC.hH hP₁).2 e₂ he₂ 1 l g₀ m hm 1 (Subgroup.one_mem _) _ (he₁.maps _ hΨ)
  rw [mul_one] at h₁
  rw [one_mul] at h₂
  have h₁' : e₁ (om (m, 1) (G.M.co.rho B.ψ (shiftA H H' l⁻¹) (om (k, h) Φ))) =
      om₂ (m, 1) (e₁ (G.M.co.rho B.ψ (shiftA H H' l⁻¹) (om (k, h) Φ))) := by
    rw [h₁]; simp
  have hν : ((X.β / X.α) l : ℂ) = (X.ν l : ℂ)⁻¹ := by
    simp [Chars.ν, MonoidHom.div_apply, Circle.coe_div, inv_div]
  rw [← hconj, hce _ (hS.pres _ _ hΨ), h₁', h₂, hce _ hΨ, map_smul]
  simp only [thetaSum_smul, hν]
  ring

end GlobalTheory.XTermLaw

end
