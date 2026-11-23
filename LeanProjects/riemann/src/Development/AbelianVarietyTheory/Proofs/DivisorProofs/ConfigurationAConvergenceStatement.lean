import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigurationAConvergence
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
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)
open GlobalTheory.FockBridge
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.configuration_a_convergence : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b)
    (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F (b + 2) a') (Rf : FinMaps F (b + 2) a')
      (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W) (R₁ : RealMaps F b a') (Rf₁ : FinMaps F b a'),
      IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
      ∀ (A : InfinitePlace F → Matrix (Fin (b + 2)) (Formalism.BasicNotions.TH.Ix (b + 2 - G.p) G.p) ℂ) (C : InfinitePlace F → Matrix (Fin (b + 2 + a')) (Formalism.BasicNotions.TH.Ix (b + 2 + a' - (G.p + G.q)) (G.p + G.q)) ℂ) (Φ : GlobalTheory.RealLift.Tens F (b + 2 - G.p) G.p (b + 2 + a' - (G.p + G.q)) (G.p + G.q) →ₗ[ℂ] SInf F (Fin (b + 2) × Fin (b + 2 + a'))), IsFockData B G.M A C Φ → ∀ N : Submodule ℂ R.Pi, N ≤ lowPartInf B G.M R.p →
      (∀ (w : InfinitePlace F) (Y : Formalism.BasicNotions.TH.Mat (b + 2 + a' - (G.p + G.q)) (G.p + G.q)), Formalism.BasicNotions.TH.IsKC Y → ∀ v ∈ N, fockOp (R.p ∘ₗ Φ) w Y v ∈ N) →
      N = ⊥ ∨ N = lowPartInf B G.M R.p := by
  first | exact @GlobalTheory.IrrBridgeLow.lowPartInf_irr_fockOp | exact GlobalTheory.IrrBridgeLow.lowPartInf_irr_fockOp | (intros; apply GlobalTheory.IrrBridgeLow.lowPartInf_irr_fockOp <;> assumption)
