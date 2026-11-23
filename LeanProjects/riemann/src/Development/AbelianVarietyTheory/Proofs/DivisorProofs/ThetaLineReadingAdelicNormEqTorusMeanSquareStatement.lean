import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLineReadingAdelicNormEqTorusMeanSquare
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodModModT

open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLineReading_adelicNorm_eq_torusMeanSquare : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (δ : ℂ) (r : D.host.E), Setup ψ θ S T ⊤ δ r →
  ∀ LT : Lat T, IsSelfDualC T LT →
    (∀ z : Matrix (Fin d) (Fin a) D.host.E, z ∈ Formalism.MainNotions.TaylorLogMetric.YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D a) (Formalism.MainNotions.StandardLatticesGL3.stdL D d) ↔
      finPt hS hT r z ∈ latO S T (stdLat S) LT fun _ => True) →
  ∀ e0 ∈ Formalism.MainNotions.TaylorLogMetric.Th D (Formalism.MainNotions.TaylorLogMetric.tor0 D ⊤ δ) (Formalism.MainNotions.StandardLatticesGL3.stdL D a) (Formalism.MainNotions.StandardLatticesGL3.stdL D d), ∀ f₀,
    Reads ψ θ hS hT ⊤ δ r e0 f₀ → IsSphOff ψ S T (stdLat S) LT ∅ f₀ →
  ∀ (ν : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) ν 𝓕 →
    ip S T ν 𝓕 f₀ f₀ = (Formalism.MainNotions.TaylorLogMetric.normSq D (Formalism.MainNotions.TaylorLogMetric.tor0 D ⊤ δ) (Formalism.MainNotions.StandardLatticesGL3.La0 D (Formalism.MainNotions.TaylorLogMetric.tor0 D ⊤ δ) a d) e0 : ℝ) := by
  first | exact @GlobalTheory.VacNormMean.ip_eq_normSq | exact GlobalTheory.VacNormMean.ip_eq_normSq | (intros; apply GlobalTheory.VacNormMean.ip_eq_normSq <;> assumption)
