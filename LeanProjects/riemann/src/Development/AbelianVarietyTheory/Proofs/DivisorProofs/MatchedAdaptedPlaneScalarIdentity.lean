import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermUnipotentIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousThetaLiftTransfer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLeftInvariantThetaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLeftInvariantDualStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairHypPlaneAdaptedLiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewSpaceFundamentalDomainIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairPlaneHyperbolicReduction

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.ThKTowerCT

theorem sFinite_restrict_haar {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (s : Set G) :
    SFinite (μ.restrict s) := inferInstance

set_option maxHeartbeats 800000 in

theorem constTerm_lift : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ)
    (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'),
    IsMatched B G X om om' R Rf →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ → ∀ c : ℂ,
      ∀ Φ ∈ PolData B G.M, ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁,
      IsCT H' (fun h => G.M.I om Φ h - c * G.M'.I om' Φ' h) 0 →
      (∀ N : ℕ, ∃ C : ℝ, ∀ h, ‖G.M.I om Φ h - c * G.M'.I om' Φ' h‖ * (qht h : ℝ) ^ N ≤ C) →
      ∀ Φ₁ ∈ PolData B G.M,
      ∀ (μ : Measure (UA σ G.W.J)) (𝓕 : Set (UA σ G.W.J)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ G.W.J) 𝓕 μ →
      ∀ (d₂ : ℕ) (H : Plane E a d₂), (d₂ + 2 = a ∧ form σ G.V.J H.x H.x = 0 ∧ form σ G.V.J H.y H.y = 0 ∧ form σ G.V.J H.x H.y = 1 ∧
          (∀ u, form σ G.V.J (H.ι *ᵥ u) H.x = 0 ∧ form σ G.V.J (H.ι *ᵥ u) H.y = 0) ∧ Function.Injective H.ι.mulVec) →
        ∀ (V₁ : Spc F E d₂) (M₁ : Model σ V₁ G.W) (e : Fn F a (a + a') →ₗ[ℂ] Fn F d₂ (a + a')),
          V₁.J = H.ιᵀ * G.V.J * H.ι.map σ → M₁.IsGood B.ψ →
          IsEv B G.M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e → ∃ C₀ : ℂ,
          IsCT (W := G.V) H (fun g : UA σ G.V.J => ∫ h in 𝓕, (G.M.I om Φ h - c * G.M'.I om' Φ' h) * (starRingEnd ℂ) (theta om Φ₁ g h) ∂μ)
            (fun g => C₀ * ∫ h in 𝓕, (G.M.I om Φ h - c * G.M'.I om' Φ' h) * (starRingEnd ℂ) (thetaSum F (e (om (g, h) Φ₁))) ∂μ) := by
  intro hK F E _ _ _ _ _ σ B a a' G X om om' R Rf hM d₁ W₁ H' i₀ i₁ hH' c Φ hΦ Φ' hΦ' hct hdec Φ₁ hΦ₁ μ 𝓕 hμ h𝓕
    d₂ H hH V₁ M₁ e hV₁ hM₁ he
  have hT := hM.triple
  have hP := (GlobalTheory.ThK.Check.isPair_of_isTriple hT).1
  have hS : Φ₁ ∈ schA F _ := GlobalTheory.ThK.SqIntCont.polData_le_schA hT.geo.hM hΦ₁
  obtain ⟨C₀, hC₀⟩ := GlobalTheory.T.pair_hyp_plane_adapted_lift hK F E σ B a (a + a') G.V G.W G.M _ _ om _ _ _ _ hP d₁ W₁ H' i₀ i₁ hH' d₂ H hH V₁ M₁ e
    hV₁ hM₁ he
  refine ⟨starRingEnd ℂ C₀, ?_⟩
  intro μN 𝓕N hμN h𝓕N h1 g
  obtain ⟨T, γ, hTc, hTu, hTp, hγ, hsum, hbd, hct'⟩ := hC₀ Φ₁ hS g
  have hfc : Continuous fun h => G.M.I om Φ h - c * G.M'.I om' Φ' h :=
    (GlobalTheory.T.continuous_left_invariant_theta hK F E σ B a a' G X om om' hT Φ hΦ).1.sub
      (continuous_const.mul (GlobalTheory.T.continuous_left_invariant_dual hK F E σ B a a' G X om om' hT Φ' hΦ').1)
  have hfinv : ∀ p ∈ ratU σ G.W.J, ∀ h, (fun h => G.M.I om Φ h - c * G.M'.I om' Φ' h) (p * h) =
      (fun h => G.M.I om Φ h - c * G.M'.I om' Φ' h) h := by
    intro p hp h
    simp only [(GlobalTheory.T.continuous_left_invariant_theta hK F E σ B a a' G X om om' hT Φ hΦ).2 p hp h,
      (GlobalTheory.T.continuous_left_invariant_dual hK F E σ B a a' G X om om' hT Φ' hΦ').2 p hp h]
  have hint := GlobalTheory.T.pair_plane_hyperbolic_reduction hK F E σ B a (a + a') G.V G.W G.M _ _ om _ _ _ _ hP d₂ H hH _ hfc hdec Φ₁ hS μ 𝓕 hμ h𝓕
    μN 𝓕N hμN h𝓕N h1 g
  obtain ⟨hvi, hv0⟩ := GlobalTheory.T.skew_space_fundamental_domain_integral hK F E σ B (a + a') d₁ G.W W₁ H' i₀ i₁ _ _ hP.base hP.skew hH' μ 𝓕 hμ h𝓕 _ hfc hfinv
    hct hdec T γ hTc hTu hTp hγ hsum hbd
  obtain ⟨i1, i2, i3, i4⟩ := GlobalTheory.UnipCT.topFacts (F := F) σ G.W.J
  haveI := i1; haveI := i2; haveI := i3; haveI := i4
  haveI : BorelSpace (UA σ G.W.J) := ⟨rfl⟩
  haveI := hμ
  have fN : IsFiniteMeasure (μN.restrict 𝓕N) := ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩
  haveI s1 : SFinite (μN.restrict 𝓕N) := @instSFiniteOfSigmaFinite _ _ _ (@IsFiniteMeasure.toSigmaFinite _ _ _ fN)
  haveI s2 : SFinite (μ.restrict 𝓕) := sFinite_restrict_haar μ 𝓕
  let Θ : unip σ G.V H → UA σ G.W.J → ℂ := fun u h =>
    (G.M.I om Φ h - c * G.M'.I om' Φ' h) * (starRingEnd ℂ) (theta om Φ₁ (u.1 * g) h)
  have hint' : Integrable (Function.uncurry Θ) ((μN.restrict 𝓕N).prod (μ.restrict 𝓕)) := hint
  have hpt : ∀ h, ∫ u in 𝓕N, Θ u h ∂μN = starRingEnd ℂ C₀ * ((G.M.I om Φ h - c * G.M'.I om' Φ' h) *
      (starRingEnd ℂ) (thetaSum F (e (om (g, h) Φ₁)))) +
      (G.M.I om Φ h - c * G.M'.I om' Φ' h) * (starRingEnd ℂ) (∑' w, T (γ w * h)) := by
    intro h
    simp only [Θ]
    rw [integral_const_mul, integral_conj, hct' μN 𝓕N hμN h𝓕N h1 h, map_add, map_mul]
    ring
  have hK : Integrable (fun h => ∫ u in 𝓕N, Θ u h ∂μN) (μ.restrict 𝓕) := hint'.integral_prod_right
  have hA : Integrable (fun h => starRingEnd ℂ C₀ * ((G.M.I om Φ h - c * G.M'.I om' Φ' h) *
      (starRingEnd ℂ) (thetaSum F (e (om (g, h) Φ₁))))) (μ.restrict 𝓕) := by
    refine (hK.sub hvi).congr (Eventually.of_forall fun h => ?_)
    simp only [Pi.sub_apply, hpt]
    ring
  change starRingEnd ℂ C₀ * ∫ h in 𝓕, (G.M.I om Φ h - c * G.M'.I om' Φ' h) *
      (starRingEnd ℂ) (thetaSum F (e (om (g, h) Φ₁))) ∂μ = ∫ u in 𝓕N, ∫ h in 𝓕, Θ u h ∂μ ∂μN
  rw [integral_integral_swap hint']
  simp only [hpt]
  rw [integral_add hA hvi, integral_const_mul, hv0, add_zero]

end GlobalTheory.ThKTowerCT
