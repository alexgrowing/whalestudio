import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPeriodSq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsMeasLevW
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsMeasDef
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsFundamentalDomain
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ClassFunctionSumIntegral

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefiniteLevelMeasure

theorem exists_isMeasDef_openCompact : ∀ {D : D7} (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))), IsDefiniteSpace V → IsOpenCompactLevel V K →
  ∃ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), Links.IsMeasDef V K μ 𝓕 := by
  intro D V K hV hK
  have hd : ∀ ρ : D.what₂.Tau, (V.sig (tauE D ρ)).1 = 0 ∨ (V.sig (tauE D ρ)).2 = 0 := by
    intro ρ
    rcases hV.2 (tauE D ρ) with h | h <;> rw [h] <;> simp
  choose ν hν hg using fun ρ => GlobalTheory.Mem.DefiniteMeasure.exists_probHaar _ _ (hd ρ)
  obtain ⟨μ, hμ⟩ := GlobalTheory.LevelMeasure.exists_isMeasLevW D V hV.1 K hK.1 hK.2
    (fun _ m => m.IsHaarMeasure ∧ IsProbabilityMeasure m) ν hν (fun ρ => (hg ρ _).2 rfl)
    (fun ρ m h => (hg ρ m).1 h)
  obtain ⟨𝓕, h𝓕⟩ := GlobalTheory.FundDomDiscrete.exists_fundDom D V μ hμ.1
  exact ⟨μ, 𝓕, hμ, h𝓕⟩

end GlobalTheory.DefiniteLevelMeasure
