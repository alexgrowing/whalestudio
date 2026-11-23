import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedDiffsRapidDecay
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

open GlobalTheory.ThK.DescB
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matched_diffs_rapid_decay : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf →
    ∀ c : ℂ, ∀ f ∈ GlobalTheory.ThK.DescB.Diffs B G X om om' R Rf c, (∀ N : ℕ, ∃ C : ℝ, ∀ h, ‖f h‖ * (qht h : ℝ) ^ N ≤ C) →
    ∀ (d₂ : ℕ) (H : Plane E a d₂), (d₂ + 2 = a ∧ form σ G.V.J H.x H.x = 0 ∧ form σ G.V.J H.y H.y = 0 ∧ form σ G.V.J H.x H.y = 1 ∧
          (∀ u, form σ G.V.J (H.ι *ᵥ u) H.x = 0 ∧ form σ G.V.J (H.ι *ᵥ u) H.y = 0) ∧ Function.Injective H.ι.mulVec) →
    ∀ (V₁ : Spc F E d₂) (M₁ : Model σ V₁ G.W) (e : Fn F a (a + a') →ₗ[ℂ] Fn F d₂ (a + a')),
      V₁.J = H.ιᵀ * G.V.J * H.ι.map σ → M₁.IsGood B.ψ →
      IsEv B G.M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
    ∀ (μ : Measure (UA σ G.W.J)) (𝓕 : Set (UA σ G.W.J)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ G.W.J) 𝓕 μ →
    ∀ (g : UA σ G.V.J), ∀ Ψ ∈ schA F (Fin a × Fin (a + a')), ∫ h in 𝓕, f h * (starRingEnd ℂ) (thetaSum F (e (om (g, h) Ψ))) ∂μ ≠ 0 →
    ∃ (ν₀ β₀ : (Fv F B.v₁)ˣ →* ℂˣ) (ℓ : Fin a → Fv F B.v₁) (ψv : AddChar (Fv F B.v₁) ℂ)
      (Bf : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + a')) (Fv F B.v₁)) →ₗ[ℂ] GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + a')) (Fv F B.v₁)) →ₗ⋆[ℂ] ℂ),
      GlobalTheory.SmGL.IsSmoothChar ν₀ ∧ GlobalTheory.SmGL.IsUnitaryChar ν₀ ∧ GlobalTheory.SmGL.IsSmoothChar β₀ ∧ GlobalTheory.SmGL.IsUnitaryChar β₀ ∧
      (∀ m : ℕ, 0 < m → ∀ r : ℝ, ((ν₀ (unifAt B.v₁) : ℂ)) ^ m ≠ (r : ℂ)) ∧ ℓ ≠ 0 ∧ Continuous ψv ∧ ψv ≠ 1 ∧ Bf ≠ 0 ∧
      (∀ (g : GL (Fin a) (Fv F B.v₁)) (Ψ₁ Ψ₁' Ψ₂ : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + a')) (Fv F B.v₁))),
        Ψ₁'.1 = GlobalTheory.SplitFlip.omA ν₀ β₀ g 1 Ψ₁.1 → Bf Ψ₁' Ψ₂ = Bf Ψ₁ Ψ₂) ∧
      (∀ (h : GL (Fin (a + a')) (Fv F B.v₁)) (Ψ₁ Ψ₁' Ψ₂ Ψ₂' : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + a')) (Fv F B.v₁))),
        Ψ₁'.1 = GlobalTheory.SplitFlip.omA ν₀ β₀ 1 h Ψ₁.1 → Ψ₂'.1 = GlobalTheory.SplitFlip.omA ν₀ β₀ 1 h Ψ₂.1 → Bf Ψ₁' Ψ₂' = Bf Ψ₁ Ψ₂) ∧
      (∀ (z : Fin (a + a') → Fv F B.v₁) (Ψ₁ Ψ₂ Ψ₂' : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + a')) (Fv F B.v₁))),
        Ψ₂'.1 = (fun Y => ψv (ℓ ⬝ᵥ (Y *ᵥ z)) * Ψ₂.1 Y) → Bf Ψ₁ Ψ₂' = Bf Ψ₁ Ψ₂) := by
  first | exact @GlobalTheory.ThK.GlobLoc.exists_local_form | exact GlobalTheory.ThK.GlobLoc.exists_local_form | (intros; apply GlobalTheory.ThK.GlobLoc.exists_local_form <;> assumption)
