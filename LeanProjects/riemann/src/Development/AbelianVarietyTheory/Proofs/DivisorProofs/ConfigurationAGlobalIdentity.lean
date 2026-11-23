import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffPartLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchOperatorCompactUnitaryWStatement
import Formalism.LocalRingCardinality.DataTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdaptedFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanEigenOrthonormalFrameExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedRealFrameExistsStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)
open GlobalTheory.FockBridge
open scoped Classical

namespace GlobalTheory.FockBridge.FramesAlpha

theorem frames_alpha : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b)
    (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F (b + 2) a') (Rf : FinMaps F (b + 2) a')
      (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W) (R₁ : RealMaps F b a') (Rf₁ : FinMaps F b a'),
      IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
      ∃ (A : InfinitePlace F → Matrix (Fin (b + 2)) (Formalism.BasicNotions.TH.Ix (b + 2 - G.p) G.p) ℂ) (C : InfinitePlace F → Matrix (Fin (b + 2 + a')) (Formalism.BasicNotions.TH.Ix (b + 2 + a' - (G.p + G.q)) (G.p + G.q)) ℂ) (r₀ : Fin (b + 2 + a' - (G.p + G.q))) (s₀ : Fin (G.p + G.q)), IsFrames B G.V G.W A C ∧ IsAdaptedFrame B H' C r₀ s₀ := by
  intro _ F E _ _ _ _ _ σ B b a' G G₁ H H' hCfg X om om' R Rf om₁ om₁' R₁ Rf₁ hM hM₁
  have hB := hM.triple.base
  have hg := hM.triple.geo
  have hg₁ := hM₁.triple.geo
  have hq := hCfg.q0
  have hq₁ := hCfg.q1
  have hp := hCfg.ep
  have ha := hg₁.aBig
  obtain ⟨r₀, s₀, C, hC, hCθ, hAd⟩ := GlobalTheory.T.adapted_real_frame_exists F E σ B (b + 2 + a') (b + a') 0 (b + 1)
    (b + 2 + a' - (G.p + G.q)) (G.p + G.q) (b + a' - (G₁.p + G₁.q)) (G₁.p + G₁.q) G.W G₁.W H' hB hg.hW hg₁.hW hCfg.hH'
    (by omega) (by omega)
  choose A hA hAθ using fun w => GlobalTheory.RealLift.frameEx_holds _ _ _ _ _ (hg.hV.sig w) (hg.hV.cartan w)
  refine ⟨A, C, r₀, s₀, ⟨⟨one_mul _, fun w => ?_, hC⟩, hAθ, hCθ⟩, hAd⟩
  rw [GlobalTheory.RealLift.Main.incM_map_piInf, one_smul]
  exact hA w

end GlobalTheory.FockBridge.FramesAlpha
