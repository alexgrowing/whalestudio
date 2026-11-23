import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteAdaptedPlaneThetaReduction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusUnitaryCharUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedDiffsRapidDecayStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

open GlobalTheory.ThK.DescB
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ThKLiftVLower

theorem lower : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
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
          IsEv B G.M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
          ∀ g : UA σ G.V.J, ∫ h in 𝓕, (G.M.I om Φ h - c * G.M'.I om' Φ' h) * (starRingEnd ℂ) (thetaSum F (e (om (g, h) Φ₁))) ∂μ = 0 := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM hq hp d₁ W₁ H' i₀ i₁ hH' c Φ Φ' hΦ' hPM hct hdec Φ₁ Φ₁' hΦ₁' hPM₁ μ 𝓕 hμ h𝓕 d₂ H hH V₁ M₁ e hV₁ hM₁ hev g
  have hS₁ : Φ₁ ∈ schA F (Fin a × Fin (a + a')) := by
    obtain ⟨T, -, m, m', u, φ, u', φ', hu, -, rfl, -⟩ := hPM₁
    exact GlobalTheory.ThK.SqIntCont.polData_le_schA hM.triple.geo.hM (GlobalTheory.ThK.LiftContA.sum_pure_mem_polData G.M T u φ hu)
  have hf : (fun h => G.M.I om Φ h - c * G.M'.I om' Φ' h) ∈ Diffs B G X om om' R Rf c :=
    Submodule.subset_span ⟨Φ, Φ', hΦ', hPM, rfl⟩
  by_contra hne
  obtain ⟨ν₀, β₀, ℓ, ψv, Bf, s1, u1, s2, u2, hnr, hℓ, hψc, hψ1, hBf, h1, h2, h3⟩ :=
    GlobalTheory.T.matched_diffs_rapid_decay hKP F E σ B a a' G X om om' R Rf hM c _ hf hdec d₂ H hH V₁ M₁ e hV₁ hM₁ hev μ 𝓕 hμ h𝓕 g Φ₁ hS₁ hne
  exact hBf (GlobalTheory.T.frobenius_unitary_char_unique (Fv F B.v₁) a a' ν₀ β₀ (unifAt B.v₁) (GlobalTheory.SplitFlip.exists_isUnif (k := Fv F B.v₁)).choose_spec
    s1 u1 s2 u2 hnr ℓ hℓ ψv hψc hψ1 Bf h1 h2 h3)

end GlobalTheory.ThKLiftVLower
