import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigurationBLocalZetaIdentity
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KEqOnId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffPartLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchOperatorCompactUnitaryWStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdaptedFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensInclInjective
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)
open Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.FockIncl

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.configuration_b_local_zeta_identity : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b)
    (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a (b + 2)) (Rf : FinMaps F a (b + 2))
      (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W) (R₁ : RealMaps F a b) (Rf₁ : FinMaps F a b),
      IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
      ∃ (P Q R₀ S₀ : ℕ) (A : InfinitePlace F → Matrix (Fin a) (Ix P Q) ℂ)
        (C₁ : InfinitePlace F → Matrix (Fin (a + b)) (Ix R₀ S₀) ℂ)
        (C : InfinitePlace F → Matrix (Fin (a + (b + 2))) (Ix (R₀ + 1) (S₀ + 1)) ℂ)
        (Φ₁ : Tens F P Q R₀ S₀ →ₗ[ℂ] SInf F (Fin a × Fin (a + b)))
        (Φ : Tens F P Q (R₀ + 1) (S₀ + 1) →ₗ[ℂ] SInf F (Fin a × Fin (a + (b + 2)))) (r₀ : Fin (R₀ + 1)) (s₀ : Fin (S₀ + 1)),
        GlobalTheory.FockBridge.IsFockData B G₁.M A C₁ Φ₁ ∧ GlobalTheory.FockBridge.IsFockData B G.M A C Φ ∧
        GlobalTheory.FockBridge.IsAdaptedFrame B H' C r₀ s₀ ∧ IsCompat B H' C C₁ r₀ s₀ := by
  first | exact @GlobalTheory.FockFrames.frames_beta | exact GlobalTheory.FockFrames.frames_beta | (intros; apply GlobalTheory.FockFrames.frames_beta <;> assumption)
