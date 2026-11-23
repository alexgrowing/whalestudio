import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermUnipotentIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftInvariantRational
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLeftInvariantThetaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLeftInvariantDualStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairHypPlaneAdaptedLiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewSpaceFundamentalDomainIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairPlaneHyperbolicReduction

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ThKTowerCT

theorem polData_fst {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {R : RealMaps F a a'} {Rf : FinMaps F a a'}
    {Φ : (Fin a × Fin (a + a') → AF F) → ℂ} {Φ' : (Fin a' × Fin (a + a') → AF F) → ℂ}
    (h : PolMatch B G X R Rf Φ Φ') : Φ ∈ PolData B G.M := by
  obtain ⟨T, -, m, m', f, φ, f', φ', hf, -, rfl, -⟩ := h
  refine Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨f i, (hf i).1, φ i, (hf i).2.1, ?_, rfl⟩
  exact Filter.mem_of_superset T.finite_toSet.compl_mem_cofinite fun v hv => (hf i).2.2 v hv

theorem polData_snd {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {R : RealMaps F a a'} {Rf : FinMaps F a a'}
    {Φ : (Fin a × Fin (a + a') → AF F) → ℂ} {Φ' : (Fin a' × Fin (a + a') → AF F) → ℂ}
    (h : PolMatch B G X R Rf Φ Φ') : Φ' ∈ PolData B G.M' := by
  obtain ⟨T, -, m, m', f, φ, f', φ', -, hf', -, rfl, -⟩ := h
  refine Submodule.sum_mem _ fun j _ => Submodule.subset_span ⟨f' j, (hf' j).1, φ' j, (hf' j).2.1, ?_, rfl⟩
  exact Filter.mem_of_superset T.finite_toSet.compl_mem_cofinite fun v hv => (hf' j).2.2 v hv

theorem unfold : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf → G.q = 0 → 1 ≤ G.p →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ → ∀ c : ℂ,
      ∀ Φ, ∀ Φ' ∈ G.M'.So B.ψ B.τ₁, PolMatch B G X R Rf Φ Φ' →
      IsCT H' (fun h => G.M.I om Φ h - c * G.M'.I om' Φ' h) 0 →
      (∀ N : ℕ, ∃ C : ℝ, ∀ h, ‖G.M.I om Φ h - c * G.M'.I om' Φ' h‖ * (qht h : ℝ) ^ N ≤ C) →
      ∀ Φ₁, ∀ Φ₁' ∈ G.M'.So B.ψ B.τ₁, PolMatch B G X R Rf Φ₁ Φ₁' →
      ∀ (μ : Measure (UA σ G.W.J)) (𝓕 : Set (UA σ G.W.J)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ G.W.J) 𝓕 μ →
      ∀ (d₂ : ℕ) (H : Plane E a d₂), (d₂ + 2 = a ∧ form σ G.V.J H.x H.x = 0 ∧ form σ G.V.J H.y H.y = 0 ∧ form σ G.V.J H.x H.y = 1 ∧
          (∀ u, form σ G.V.J (H.ι *ᵥ u) H.x = 0 ∧ form σ G.V.J (H.ι *ᵥ u) H.y = 0) ∧ Function.Injective H.ι.mulVec) →
        ∀ (V₁ : Spc F E d₂) (M₁ : Model σ V₁ G.W) (e : Fn F a (a + a') →ₗ[ℂ] Fn F d₂ (a + a')),
          V₁.J = H.ιᵀ * G.V.J * H.ι.map σ → M₁.IsGood B.ψ →
          IsEv B G.M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e → ∃ C₀ : ℂ,
          IsCT (W := G.V) H (fun g : UA σ G.V.J => ∫ h in 𝓕, (G.M.I om Φ h - c * G.M'.I om' Φ' h) * (starRingEnd ℂ) (theta om Φ₁ g h) ∂μ)
            (fun g => C₀ * ∫ h in 𝓕, (G.M.I om Φ h - c * G.M'.I om' Φ' h) * (starRingEnd ℂ) (thetaSum F (e (om (g, h) Φ₁))) ∂μ) := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM hq hp d₁ W₁ H' i₀ i₁ hH' c Φ Φ' hΦ' hPM hct hdec Φ₁ Φ₁' hΦ₁'
    hPM₁ μ 𝓕 hμ h𝓕 d₂ H hH V₁ M₁ e hJ hM₁ he
  have hT := hM.triple
  have hP := (GlobalTheory.ThK.Check.isPair_of_isTriple hT).1
  have hΦ₁S : Φ₁ ∈ schA F (Fin a × Fin (a + a')) := GlobalTheory.ThK.LeftInvV.polData_le_schA hT.geo.hM (polData_fst hPM₁)
  obtain ⟨hc1, hr1⟩ := GlobalTheory.T.continuous_left_invariant_theta hKP F E σ B a a' G X om om' hT Φ (polData_fst hPM)
  obtain ⟨hc2, hr2⟩ := GlobalTheory.T.continuous_left_invariant_dual hKP F E σ B a a' G X om om' hT Φ' ⟨polData_snd hPM, hΦ'⟩
  have hfc : Continuous (fun h => G.M.I om Φ h - c * G.M'.I om' Φ' h) := hc1.sub (continuous_const.mul hc2)
  have hfr : ∀ p ∈ ratU σ G.W.J, ∀ h, G.M.I om Φ (p * h) - c * G.M'.I om' Φ' (p * h) = G.M.I om Φ h - c * G.M'.I om' Φ' h :=
    fun p hp h => by rw [hr1 p hp h, hr2 p hp h]
  obtain ⟨C₀, hC⟩ := GlobalTheory.T.pair_hyp_plane_adapted_lift hKP F E σ B a (a + a') G.V G.W G.M _ _ om _ _ _ _ hP d₁ W₁ H' i₀ i₁ hH' d₂ H hH V₁ M₁ e hJ hM₁ he
  refine ⟨starRingEnd ℂ C₀, ?_⟩
  intro μN 𝓕N hN h𝓕N hmass g
  obtain ⟨T, γ, hTc, hTu, hTp, hγ, hsum, hbd, hct1⟩ := hC Φ₁ hΦ₁S g
  have hint := GlobalTheory.T.pair_plane_hyperbolic_reduction hKP F E σ B a (a + a') G.V G.W G.M _ _ om _ _ _ _ hP d₂ H hH _ hfc hdec Φ₁ hΦ₁S μ 𝓕 hμ h𝓕 μN 𝓕N hN h𝓕N
    hmass g
  obtain ⟨hI2, h0⟩ := GlobalTheory.T.skew_space_fundamental_domain_integral hKP F E σ B (a + a') d₁ G.W W₁ H' i₀ i₁ _ _ hT.base hT.geo.hW hH' μ 𝓕 hμ h𝓕 _ hfc hfr hct hdec T γ hTc
    hTu hTp hγ hsum hbd
  obtain ⟨i1, i2, i3, i4⟩ := GlobalTheory.UnipCT.topFacts σ G.W.J
  haveI : BorelSpace (UA σ G.W.J) := ⟨rfl⟩
  haveI hNf : IsFiniteMeasure (μN.restrict 𝓕N) := ⟨by rw [Measure.restrict_apply_univ, hmass]; exact ENNReal.one_lt_top⟩
  haveI : SFinite (μN.restrict 𝓕N) := @instSFiniteOfSigmaFinite _ _ _ (@IsFiniteMeasure.toSigmaFinite _ _ _ hNf)
  have key : ∀ h, ∫ u in 𝓕N, (G.M.I om Φ h - c * G.M'.I om' Φ' h) * (starRingEnd ℂ) (theta om Φ₁ (u.1 * g) h) ∂μN =
      (G.M.I om Φ h - c * G.M'.I om' Φ' h) * (starRingEnd ℂ) (C₀ * thetaSum F (e (om (g, h) Φ₁))) +
        (G.M.I om Φ h - c * G.M'.I om' Φ' h) * (starRingEnd ℂ) (∑' w, T (γ w * h)) := by
    intro h
    rw [integral_const_mul, integral_conj, hct1 μN 𝓕N hN h𝓕N hmass h, map_add, mul_add]
  haveI : SigmaCompactSpace (UA σ G.W.J) := inferInstance
  haveI : SigmaFinite μ := inferInstance
  haveI : SFinite μ := instSFiniteOfSigmaFinite
  haveI : SigmaFinite (μ.restrict 𝓕) := MeasureTheory.Restrict.sigmaFinite μ 𝓕
  haveI : SFinite (μ.restrict 𝓕) := @instSFiniteOfSigmaFinite _ _ _ this
  have hI : Integrable (fun h => (G.M.I om Φ h - c * G.M'.I om' Φ' h) * (starRingEnd ℂ) (C₀ * thetaSum F (e (om (g, h) Φ₁))) +
        (G.M.I om Φ h - c * G.M'.I om' Φ' h) * (starRingEnd ℂ) (∑' w, T (γ w * h))) (μ.restrict 𝓕) :=
    hint.integral_prod_right.congr (Filter.Eventually.of_forall fun h => key h)
  have hI1 : Integrable (fun h => (G.M.I om Φ h - c * G.M'.I om' Φ' h) *
      (starRingEnd ℂ) (C₀ * thetaSum F (e (om (g, h) Φ₁)))) (μ.restrict 𝓕) :=
    (hI.sub hI2).congr (Filter.Eventually.of_forall fun h => by simp)
  rw [integral_integral_swap hint]
  simp_rw [key]
  rw [integral_add hI1 hI2, h0, add_zero, ← integral_const_mul]
  congr 1
  funext h
  rw [map_mul]
  ring

end GlobalTheory.ThKTowerCT

end
