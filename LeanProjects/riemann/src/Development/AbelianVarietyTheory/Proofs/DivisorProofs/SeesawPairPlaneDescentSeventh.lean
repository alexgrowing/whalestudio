import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawPairPlaneDescentFourthStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawPairPlaneDescentEleventhStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawPairHyperbolicPlane
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawPairPlaneDescentTwelfthStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ThKBoundW

theorem bound : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ (d₂ : ℕ) (H : Plane E n d₂), (d₂ + 2 = n ∧ form σ X.J H.x H.x = 0 ∧ form σ X.J H.y H.y = 0 ∧ form σ X.J H.x H.y = 1 ∧
        (∀ u, form σ X.J (H.ι *ᵥ u) H.x = 0 ∧ form σ X.J (H.ι *ᵥ u) H.y = 0) ∧ Function.Injective H.ι.mulVec) →
    ∀ (V₁ : Spc F E d₂) (M₁ : Model σ V₁ W) (e : Fn F n d →ₗ[ℂ] Fn F d₂ d),
      V₁.J = H.ιᵀ * X.J * H.ι.map σ → M₁.IsGood B.ψ → IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
    ∀ (μ : Measure (unip σ X H)) (𝓕 : Set (unip σ X H)), μ.IsHaarMeasure →
      IsFundamentalDomain ((ratU σ X.J).subgroupOf (unip σ X H)) 𝓕 μ → μ 𝓕 = 1 →
    ∀ Φ ∈ schA F (Fin n × Fin d), ∀ g : UA σ X.J,
      ∃ (C : ℝ) (k : ℕ), ∀ h : UA σ W.J, Summable (fun w : Fin d → E => ‖∫ u in 𝓕, thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (om (u.1, 1) (om (g, h) Φ)))) ∂μ‖) ∧
        ∑' w : Fin d → E, ‖∫ u in 𝓕, thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (om (u.1, 1) (om (g, h) Φ)))) ∂μ‖ ≤ C * (qht h : ℝ) ^ k := by
  intro hKP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ hH' d₂ H hH V₁ M₁ e hV₁ hM₁ he μ 𝓕 hμ h𝓕 h1 Φ hΦ g
  have hS := IsUWeilPair.isUSplitting hP.weil
  have hpres : ∀ x, ∀ Φ ∈ schA F (Fin n × Fin d), om x Φ ∈ schA F (Fin n × Fin d) := fun x Φ hΦ => hS.pres x Φ hΦ
  obtain ⟨K, hKc, hKsub, hKfd⟩ := GlobalTheory.T.seesaw_pair_hyperbolic_plane hKP F E σ B n d X W M χX χW om r s r' s' hP d₂ H hH
  obtain ⟨C, k, hCK⟩ := GlobalTheory.T.seesaw_pair_plane_descent_twelfth hKP F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ hH' d₂ H hH V₁ M₁ e hV₁ hM₁ he
    Φ hΦ g K hKc hKsub

  have unif : ∀ u ∈ unip σ X H, ∀ h : UA σ W.J,
      Summable (fun w : Fin d → E => ‖thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (om (u, 1) (om (g, h) Φ))))‖) ∧
      ∑' w : Fin d → E, ‖thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (om (u, 1) (om (g, h) Φ))))‖ ≤ C * (ht h : ℝ) ^ k := by
    intro u hu h
    obtain ⟨γ, hγ, hγu, hK⟩ := hKfd u hu
    have heq : (fun w : Fin d → E => ‖thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (om (u, 1) (om (g, h) Φ))))‖) =
        fun w => ‖thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (om (γ * u, 1) (om (g, h) Φ))))‖ := by
      funext w
      have e1 : ((γ * u, 1) : UA σ X.J × UA σ W.J) = (γ, 1) * (u, 1) := by simp
      rw [e1, map_mul, Module.End.mul_apply]
      exact (GlobalTheory.T.seesaw_pair_plane_descent_eleventh hKP F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ hH' d₂ H hH V₁ M₁ e hV₁ hM₁ he
        γ hγ hγu _ (hpres _ _ (hpres _ _ hΦ)) w).symm
    rw [heq]
    exact hCK _ hK h
  have hC0 : ∀ h : UA σ W.J, 0 ≤ C * (ht h : ℝ) ^ k := fun h =>
    (tsum_nonneg fun w => norm_nonneg _).trans (unif 1 (one_mem _) h).2

  have integ : ∀ h : UA σ W.J,
      Summable (fun w : Fin d → E => ‖∫ u in 𝓕, thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (om (u.1, 1) (om (g, h) Φ)))) ∂μ‖) ∧
      ∑' w : Fin d → E, ‖∫ u in 𝓕, thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (om (u.1, 1) (om (g, h) Φ)))) ∂μ‖ ≤ C * (ht h : ℝ) ^ k := by
    intro h
    set f : (Fin d → E) → unip σ X H → ℂ := fun w u =>
      thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (om (u.1, 1) (om (g, h) Φ)))) with hf
    set Bd := C * (ht h : ℝ) ^ k with hBd
    have hpt : ∀ u : unip σ X H, ∀ s : Finset (Fin d → E), ∑ w ∈ s, ‖f w u‖ ≤ Bd := fun u s =>
      ((unif u.1 u.2 h).1.sum_le_tsum s fun w _ => norm_nonneg _).trans (unif u.1 u.2 h).2
    have hsum : ∀ s : Finset (Fin d → E), ∑ w ∈ s, ‖∫ u in 𝓕, f w u ∂μ‖ ≤ Bd := by
      intro s
      have h2 : ∀ w, ‖∫ u in 𝓕, f w u ∂μ‖ ≤ (∫⁻ u in 𝓕, ENNReal.ofReal ‖f w u‖ ∂μ).toReal := fun w =>
        norm_integral_le_lintegral_norm _
      have hlin : ∑ w ∈ s, ∫⁻ u in 𝓕, ENNReal.ofReal ‖f w u‖ ∂μ ≤ ∫⁻ u in 𝓕, ∑ w ∈ s, ENNReal.ofReal ‖f w u‖ ∂μ := by
        classical
        induction s using Finset.induction_on with
        | empty => simp only [Finset.sum_empty]; exact zero_le
        | insert a s ha ih =>
          rw [Finset.sum_insert ha]
          refine (add_le_add le_rfl ih).trans ?_
          refine (le_lintegral_add _ _).trans (le_of_eq ?_)
          congr 1
          funext u
          rw [Finset.sum_insert ha]
      have hup : ∫⁻ u in 𝓕, ∑ w ∈ s, ENNReal.ofReal ‖f w u‖ ∂μ ≤ ENNReal.ofReal Bd := by
        calc ∫⁻ u in 𝓕, ∑ w ∈ s, ENNReal.ofReal ‖f w u‖ ∂μ ≤ ∫⁻ _ in 𝓕, ENNReal.ofReal Bd ∂μ := by
              refine lintegral_mono fun u => ?_
              rw [← ENNReal.ofReal_sum_of_nonneg fun w _ => norm_nonneg _]
              exact ENNReal.ofReal_le_ofReal (hpt u s)
          _ = ENNReal.ofReal Bd := by
              rw [setLIntegral_const, h1, mul_one]
      have hfin : ∀ w ∈ s, ∫⁻ u in 𝓕, ENNReal.ofReal ‖f w u‖ ∂μ ≠ ⊤ := by
        intro w hw
        refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := Bd)) ?_
        refine le_trans ?_ hup
        exact Finset.single_le_sum (f := fun w => ∫⁻ u in 𝓕, ENNReal.ofReal ‖f w u‖ ∂μ) (fun _ _ => zero_le) hw |>.trans hlin
      calc ∑ w ∈ s, ‖∫ u in 𝓕, f w u ∂μ‖ ≤ ∑ w ∈ s, (∫⁻ u in 𝓕, ENNReal.ofReal ‖f w u‖ ∂μ).toReal :=
            Finset.sum_le_sum fun w _ => h2 w
        _ = (∑ w ∈ s, ∫⁻ u in 𝓕, ENNReal.ofReal ‖f w u‖ ∂μ).toReal := (ENNReal.toReal_sum hfin).symm
        _ ≤ Bd := ENNReal.toReal_le_of_le_ofReal (hC0 h) (hlin.trans hup)
    exact ⟨summable_of_sum_le (fun w => norm_nonneg _) hsum, Real.tsum_le_of_sum_le (fun w => norm_nonneg _) hsum⟩

  have reidx : ∀ γ ∈ ratU σ W.J, ∀ h : UA σ W.J,
      ∑' w : Fin d → E, ‖∫ u in 𝓕, thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (om (u.1, 1) (om (g, γ * h) Φ)))) ∂μ‖ =
      ∑' w : Fin d → E, ‖∫ u in 𝓕, thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (om (u.1, 1) (om (g, h) Φ)))) ∂μ‖ := by
    intro γ hγ h
    obtain ⟨γ₀, hγ₀⟩ := (Subgroup.mem_subgroupOf.mp hγ)
    have hmat : ∀ w : Fin d → E, mat γ *ᵥ incV F w = incV F ((γ₀ : Matrix (Fin d) (Fin d) E) *ᵥ w) := by
      intro w
      funext i
      have : mat γ = (γ₀ : Matrix (Fin d) (Fin d) E).map (inclR (F := F) (AF F)) := by
        simp only [mat, ← hγ₀]
        rfl
      rw [this]
      simp only [incV]
      rw [RingHom.map_mulVec]
      rfl
    let ev : (Fin d → E) ≃ (Fin d → E) :=
      { toFun := fun w => (γ₀ : Matrix (Fin d) (Fin d) E) *ᵥ w
        invFun := fun w => ((γ₀⁻¹ : GL (Fin d) E) : Matrix (Fin d) (Fin d) E) *ᵥ w
        left_inv := fun w => by simp [Matrix.mulVec_mulVec]
        right_inv := fun w => by simp [Matrix.mulVec_mulVec] }
    rw [← ev.tsum_eq]
    refine tsum_congr fun w => ?_
    congr 2
    funext u
    have hprod : ((u.1, 1) : UA σ X.J × UA σ W.J) * (g, γ * h) = (1, γ) * ((u.1, 1) * (g, h)) := by
      simp [Prod.mk_mul_mk]
    have e2 : om (u.1, 1) (om (g, γ * h) Φ) = om (1, γ) (om (u.1, 1) (om (g, h) Φ)) := by
      calc om (u.1, 1) (om (g, γ * h) Φ) = om ((u.1, 1) * (g, γ * h)) Φ := by rw [map_mul, Module.End.mul_apply]
        _ = om ((1, γ) * ((u.1, 1) * (g, h))) Φ := by rw [hprod]
        _ = _ := by rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
    rw [e2]
    exact GlobalTheory.T.seesaw_pair_plane_descent_fourth hKP F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ hH' d₂ H hH V₁ M₁ e hV₁ hM₁ he
      γ hγ w (ev w) (hmat w) _ (hpres _ _ (hpres _ _ hΦ))

  refine ⟨|C|, k, fun h => ⟨(integ h).1, ?_⟩⟩
  have hle : ∀ γ : ratU σ W.J,
      ∑' w : Fin d → E, ‖∫ u in 𝓕, thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (om (u.1, 1) (om (g, h) Φ)))) ∂μ‖ ≤
        |C| * (ht (γ.1 * h) : ℝ) ^ k := by
    intro γ
    rw [← reidx γ.1 γ.2 h]
    exact (integ _).2.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
  let c : ℝ≥0 := ⟨|C|, abs_nonneg C⟩
  have hm : c * (⨅ γ : ratU σ W.J, ht (γ.1 * h)) ^ k = ⨅ γ : ratU σ W.J, c * ht (γ.1 * h) ^ k :=
    Monotone.map_ciInf_of_continuousAt (f := fun t : ℝ≥0 => c * t ^ k) (by fun_prop)
      (fun a b hab => by dsimp only; gcongr) (OrderBot.bddBelow _)
  have hR : |C| * (qht h : ℝ) ^ k = ((c * (⨅ γ : ratU σ W.J, ht (γ.1 * h)) ^ k : ℝ≥0) : ℝ) := by
    simp only [qht, NNReal.coe_mul, NNReal.coe_pow]
    rfl
  rw [hR, hm, NNReal.coe_iInf]
  exact le_ciInf fun γ => by
    simp only [NNReal.coe_mul, NNReal.coe_pow]
    exact hle γ

end GlobalTheory.ThKBoundW

end
