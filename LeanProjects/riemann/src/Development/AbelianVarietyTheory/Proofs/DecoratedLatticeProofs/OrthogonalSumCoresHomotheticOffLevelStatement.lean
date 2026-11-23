import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrthogonalSumCoresHomotheticOffLevel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneAtOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthogonalSumCores_homothetic_off_level : ∀ (D : D7) (S A L : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (M M' : Lat S) (LA : Lat A) (LL : Lat L) (μ : D.host.E) (T : ℕ) (v : GlobalTheory.FinPl.Pl D) (a₀ : GA D A), IsLineVec L ζ → IsSelfDualC L LL → OrthAt o M LA LL v → TraceAt o a₀ LA M' v → SplitsAt o M' v → μ ≠ 0 → LineAt (vecB o ζ) μ M' v → star ζ ⬝ᵥ L.gram *ᵥ ζ = -(μ * star μ * (T : D.host.E)) → (T : 𝓞 D.host.F) ∉ v.asIdeal → ∃ (a : GA D A) (c : AE D), CenAt A v a ∧ NormOneAt v c ∧ SMoves S c (o.emb (a₀ * a, 1)) M M' v := by
  first | exact @GlobalTheory.Core.Mi.LatMatch.coreOff_homothetic | exact GlobalTheory.Core.Mi.LatMatch.coreOff_homothetic | (intros; apply GlobalTheory.Core.Mi.LatMatch.coreOff_homothetic <;> assumption)
