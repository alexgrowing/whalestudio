import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousPairedKernelFlatMapWeilTranslate
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.XLastLin
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_pairedKernel_flatMap_weilTranslate : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacL D (σ + 1)) (B : BesL D σ) (s : StFB ψ J B) (vL : VolM D B.L.rank J.W₀.rank) (χ χz : (AE D)ˣ →* Circle) (omz : Om J.W₀ B.L), IsWeilDatumO ψ J.W₀ B.L χ χz omz → ∀ (Φ₀ : WO J.W₀ B.L → ℂ) (Φ : WO J.W B.V → ℂ), IsThetaFunO ψ J.W₀ B.L Φ₀ → IsThetaFunO ψ J.W B.V Φ → Continuous fun q : GA D B.V × GA D J.W₀ × GA D B.A => contractT B.o J.W₀ vL.μ vL.𝓕 (s.om₀ (q.2.1, B.o.emb (q.2.2, 1)) (flFB s (s.om (1, q.1) Φ))) (omz (q.2.1, 1) Φ₀) 0 := by
  first | exact @GlobalTheory.KerContFB.kerFB_continuous | exact GlobalTheory.KerContFB.kerFB_continuous | (intros; apply GlobalTheory.KerContFB.kerFB_continuous <;> assumption)
