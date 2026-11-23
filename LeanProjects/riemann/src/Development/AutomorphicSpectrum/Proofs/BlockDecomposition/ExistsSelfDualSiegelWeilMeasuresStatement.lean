import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSelfDualSiegelWeilMeasures
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaPartD
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_self_dual_siegel_weil_measures : ∀ (D : D7) (r : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ →
  ∀ μ : Measure (Mx D V.rank r), (∃ 𝓕, IsCovolOne (ratMx D V.rank r) μ 𝓕) →
  ∀ lam : Measure (hermA D r), (∃ 𝓖, IsCovolOneH lam 𝓖) →
  ∃ (dx : Measure (Fin r → Fin V.rank → AE D)) (db : Measure (HermR (AF D.host.F) D.sp.cm.sig r)),
    SdW D.host.F D.host.E D.sp.cm.sig V.rank V.gram (AF D.host.F) ψ r dx ∧
    SdHerm D.host.F D.host.E D.sp.cm.sig (AF D.host.F) ψ r db ∧
    ∀ (φ : Mx D V.rank r → ℂ) (β : HermE D r),
      W ψ V μ lam φ β = coefN D.sp.cm.sig V.gram ψ dx db (fun X => φ (tupOf X)) β.1 := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.whit_eq_coefN | exact GlobalTheory.CompanionTheory.SiegelND.whit_eq_coefN | (intros; apply GlobalTheory.CompanionTheory.SiegelND.whit_eq_coefN <;> assumption)
