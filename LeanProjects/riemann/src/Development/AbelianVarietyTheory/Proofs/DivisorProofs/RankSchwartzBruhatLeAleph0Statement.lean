import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankSchwartzBruhatLeAleph0
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisFin
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.FinHeis
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_schwartz_bruhat_le_aleph0 : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], Module.rank ℂ (SB (κ → Af F)) ≤ Cardinal.aleph0 := by
  first | exact @GlobalTheory.SBCountAdele.rank_sb_finiteAdele_le | exact GlobalTheory.SBCountAdele.rank_sb_finiteAdele_le | (intros; apply GlobalTheory.SBCountAdele.rank_sb_finiteAdele_le <;> assumption)
