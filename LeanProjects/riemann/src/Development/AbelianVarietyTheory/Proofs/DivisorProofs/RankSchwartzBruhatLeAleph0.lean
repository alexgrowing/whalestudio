import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisFin
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RankSchwartzBruhatFinitePlaceCompletionLeAleph0
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.FinHeis

namespace GlobalTheory.SBCountAdele

theorem rank_sb_finiteAdele_le :
    ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ],
      Module.rank ℂ (SB (κ → Af F)) ≤ Cardinal.aleph0 := by
  intro F _ _ κ _
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  exact GlobalTheory.SBCount.rank_sb_le_aleph0 _

end GlobalTheory.SBCountAdele
