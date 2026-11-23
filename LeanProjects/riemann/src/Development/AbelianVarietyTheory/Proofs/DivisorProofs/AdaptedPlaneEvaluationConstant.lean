import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerRestrictionRankStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerRestrictionPairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerRestrictionCharacterStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerRestrictionUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerDoubleRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerDoubleRestrictionPairStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThKConstTerm

theorem constantTerm_theta : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁)
    (M : Model σ X W) (M₁ : Model σ X W₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B W W₁ i₀ i₁ → M₁.IsGood B.ψ →
    ∀ e₀, IsEv B M M₁ 1 H'.ι (iso0 n H') e₀ → ∃ C₀ : ℂ, C₀ ≠ 0 ∧
      ((∀ x, form σ X.J x x = 0 → x = 0) → ∀ χX χW om r s r' s', IsPair B M χX χW om r s r' s' → ∀ Φ ∈ schA F (Fin n × Fin d), ∀ g,
        IsCT H' (theta om Φ g) fun h => C₀ * thetaSum F (e₀ (om (g, h) Φ))) ∧
      ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₂ : Model σ X₁ W₁), H.IsAdapted σ B X X₁ j₀ j₁ → M₂.IsGood B.ψ →
        ∀ e, IsEv B M M₂ H.ι H'.ι (isoA H H') e → ∃ C₁ : ℂ, C₁ ≠ 0 ∧
        ∀ γ : {x : Fin n → E // x ≠ 0 ∧ form σ X.J x x = 0} → UA σ X.J,
          (∀ x, γ x ∈ ratU σ X.J ∧ mat (γ x) *ᵥ incV F x.1 = incV F H.x) →
          ∀ χX χW om r s r' s', IsPair B M χX χW om r s r' s' → ∀ Φ ∈ schA F (Fin n × Fin d), ∀ g,
            (∀ h, Summable fun x => thetaSum F (e (M.co.rho B.ψ (shiftA H H' 1) (om (γ x * g, h) Φ)))) ∧
            IsCT H' (theta om Φ g) fun h => C₀ * thetaSum F (e₀ (om (g, h) Φ)) +
              C₁ * ∑' x, thetaSum F (e (M.co.rho B.ψ (shiftA H H' 1) (om (γ x * g, h) Φ))) := by
  intro hKP F E _ _ _ _ _ σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH' hM₁ e₀ he₀
  by_cases hQ : B.IsGood σ ∧ M.IsGood B.ψ ∧ ∃ r s r' s' : ℕ, X.IsHerm σ B r s ∧ W.IsSkew σ B r' s'
  swap
  · refine ⟨1, one_ne_zero, fun _ χX χW om r s r' s' hP => (hQ ⟨hP.base, hP.good, r, s, r', s', hP.herm, hP.skew⟩).elim, ?_⟩
    intro n₁ X₁ H j₀ j₁ M₂ _ _ e _
    exact ⟨1, one_ne_zero, fun γ _ χX χW om r s r' s' hP => (hQ ⟨hP.base, hP.good, r, s, r', s', hP.herm, hP.skew⟩).elim⟩
  obtain ⟨hB, hM, hXW⟩ := hQ
  obtain ⟨C₀, hC₀, hexp⟩ := GlobalTheory.T.eigen_intertwiner_restriction_rank hKP F E σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH' hM₁ e₀ he₀ hB hM hXW

  have key : ∀ (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
      ∀ (μ : Measure (unip σ W H')) (𝓕 : Set (unip σ W H')), μ.IsHaarMeasure →
      IsFundamentalDomain ((ratU σ W.J).subgroupOf (unip σ W H')) 𝓕 μ → μ 𝓕 = 1 →
      ∀ Φ ∈ schA F (Fin n × Fin d), ∀ g h,
        (Summable fun ξ : Fin n → E => ∫ u in 𝓕, thetaSum F (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) (om (1, u.1) (om (g, h) Φ)))) ∂μ) ∧
        ∫ u in 𝓕, theta om Φ g (u.1 * h) ∂μ =
          C₀ * ∑' ξ : Fin n → E, ∫ u in 𝓕, thetaSum F (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) (om (1, u.1) (om (g, h) Φ)))) ∂μ := by
    intro χX χW om r s r' s' hP μ 𝓕 hμ h𝓕 h1 Φ hΦ g h
    have hpres : ∀ x, ∀ Φ ∈ schA F (Fin n × Fin d), om x Φ ∈ schA F (Fin n × Fin d) :=
      fun x Φ hΦ => (IsUWeilPair.isUSplitting hP.weil).pres x Φ hΦ
    have hΨ := hpres (g, h) Φ hΦ
    obtain ⟨hs, hsw⟩ := GlobalTheory.T.eigen_intertwiner_restriction_character hKP F E σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH' hM₁ e₀ he₀ χX χW om r s r' s' hP μ 𝓕 hμ h𝓕 h1 _ hΨ
    refine ⟨hs, ?_⟩
    rw [← hsw, ← integral_const_mul]
    congr 1
    funext u
    have e1 : ((g, u.1 * h) : UA σ X.J × UA σ W.J) = (1, u.1) * (g, h) := by simp
    rw [theta, e1, map_mul, Module.End.mul_apply]
    exact (hexp _ (hpres _ _ hΨ)).2

  have zero : ∀ (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
      ∀ (μ : Measure (unip σ W H')) (𝓕 : Set (unip σ W H')), μ 𝓕 = 1 → ∀ Ψ ∈ schA F (Fin n × Fin d),
        ∫ u in 𝓕, thetaSum F (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F 0) (incV F H'.y)) (om (1, u.1) Ψ))) ∂μ =
          thetaSum F (e₀ Ψ) := by
    intro χX χW om r s r' s' hP μ 𝓕 h1 Ψ hΨ
    have e2 : ∀ u : unip σ W H', thetaSum F (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F 0) (incV F H'.y)) (om (1, u.1) Ψ))) =
        thetaSum F (e₀ Ψ) := by
      intro u
      have hz : M.co.rho B.ψ (Matrix.vecMulVec (incV F 0) (incV F H'.y)) (om (1, u.1) Ψ) = om (1, u.1) Ψ := by
        have h0 : incV F (0 : Fin n → E) = 0 := by
          funext i
          unfold incV
          simp
        funext x
        simp [Darboux.rho, schr, h0]
      rw [hz, GlobalTheory.T.eigen_intertwiner_restriction_pair hKP F E σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH' hM₁ e₀ he₀ χX χW om r s r' s' hP u.1 u.2 Ψ hΨ]
    simp only [e2, setIntegral_const, measureReal_def, h1, ENNReal.toReal_one, one_smul]
  refine ⟨C₀, hC₀, ?_, ?_⟩
  · intro hanis χX χW om r s r' s' hP Φ hΦ g μ 𝓕 hμ h𝓕 h1 h
    obtain ⟨-, hk⟩ := key χX χW om r s r' s' hP μ 𝓕 hμ h𝓕 h1 Φ hΦ g h
    have hΨ : om (g, h) Φ ∈ schA F (Fin n × Fin d) := (IsUWeilPair.isUSplitting hP.weil).pres _ Φ hΦ
    rw [hk, tsum_eq_single 0, zero χX χW om r s r' s' hP μ 𝓕 h1 _ hΨ]
    intro ξ hξ
    exact GlobalTheory.T.eigen_intertwiner_restriction_unitary hKP F E σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH' hM₁ e₀ he₀ χX χW om r s r' s' hP μ 𝓕 hμ h𝓕 h1 _ hΨ ξ
      (fun h0 => hξ (hanis ξ h0))
  · intro n₁ X₁ H j₀ j₁ M₂ hH hM₂ e he
    obtain ⟨C, hC, hiso⟩ := GlobalTheory.T.eigen_intertwiner_double_restriction hKP F E σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH' hM₁ e₀ he₀ n₁ X₁ H j₀ j₁ M₂ hH hM₂ e he
    refine ⟨C₀ * C, mul_ne_zero hC₀ hC, fun γ hγ χX χW om r s r' s' hP Φ hΦ g => ⟨fun h => ?_, ?_⟩⟩
    · have hΨ : om (g, h) Φ ∈ schA F (Fin n × Fin d) := (IsUWeilPair.isUSplitting hP.weil).pres _ Φ hΦ
      have := GlobalTheory.T.eigen_intertwiner_double_restriction_pair hKP F E σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH' hM₁ e₀ he₀ n₁ X₁ H j₀ j₁ M₂ hH hM₂ e he γ hγ
        χX χW om r s r' s' hP _ hΨ
      refine this.congr fun x => ?_
      have e1 : ((γ x * g, h) : UA σ X.J × UA σ W.J) = (γ x, 1) * (g, h) := by simp
      rw [e1, map_mul, Module.End.mul_apply]
    · intro μ 𝓕 hμ h𝓕 h1 h
      have hΨ : om (g, h) Φ ∈ schA F (Fin n × Fin d) := (IsUWeilPair.isUSplitting hP.weil).pres _ Φ hΦ
      obtain ⟨hs, hk⟩ := key χX χW om r s r' s' hP μ 𝓕 hμ h𝓕 h1 Φ hΦ g h
      rw [hk]
      classical
      set a : (Fin n → E) → ℂ := fun ξ => ∫ u in 𝓕, thetaSum F (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) (om (1, u.1) (om (g, h) Φ)))) ∂μ with ha
      have hsupp : Function.support (fun ξ => if ξ = 0 then 0 else a ξ) ⊆ {x | x ≠ 0 ∧ form σ X.J x x = 0} := by
        intro ξ hξ
        simp only [Function.mem_support, ne_eq, ite_eq_left_iff, not_forall] at hξ
        obtain ⟨h0, hne⟩ := hξ
        refine ⟨h0, ?_⟩
        by_contra hf
        exact hne (GlobalTheory.T.eigen_intertwiner_restriction_unitary hKP F E σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH' hM₁ e₀ he₀ χX χW om r s r' s' hP μ 𝓕 hμ h𝓕 h1 _ hΨ ξ hf)
      rw [hs.tsum_eq_add_tsum_ite 0, ← tsum_subtype_eq_of_support_subset hsupp]
      have hval : ∀ x : {x : Fin n → E | x ≠ 0 ∧ form σ X.J x x = 0},
          (if (x : Fin n → E) = 0 then 0 else a x) =
            C * thetaSum F (e (M.co.rho B.ψ (shiftA H H' 1) (om (γ ⟨x.1, x.2⟩ * g, h) Φ))) := by
        intro x
        rw [if_neg x.2.1]
        have e1 : ((γ ⟨x.1, x.2⟩ * g, h) : UA σ X.J × UA σ W.J) = (γ ⟨x.1, x.2⟩, 1) * (g, h) := by simp
        rw [e1, map_mul, Module.End.mul_apply]
        exact hiso χX χW om r s r' s' hP μ 𝓕 hμ h𝓕 h1 _ hΨ x.1 x.2.1 x.2.2 _ (hγ ⟨x.1, x.2⟩).1 (hγ ⟨x.1, x.2⟩).2
      rw [tsum_congr hval, tsum_mul_left]
      have hz := zero χX χW om r s r' s' hP μ 𝓕 h1 _ hΨ
      simp only [ha, hz]
      beta_reduce
      rw [mul_add, ← mul_assoc]
      rfl

end GlobalTheory.ThKConstTerm

end
