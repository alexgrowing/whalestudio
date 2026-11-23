import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfCompactOpen
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid

theorem level_conj_commensurable : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (g : G.GAf),
    Subgroup.Commensurable (L.K.toSubgroup.map (MulAut.conj g).toMonoidHom) L.K.toSubgroup := by
  intro p _ G L g
  obtain ⟨hc', ho'⟩ := GlobalTheory.RelIndexCompact.conj_map_isCompact_isOpen L.K.toSubgroup g L.compact L.K.isOpen
  exact ⟨GlobalTheory.RelIndexCompact.relIndex_ne_zero_of_compact_open L.compact ho',
    GlobalTheory.RelIndexCompact.relIndex_ne_zero_of_compact_open hc' L.K.isOpen⟩

end GlobalTheory.LKMid
