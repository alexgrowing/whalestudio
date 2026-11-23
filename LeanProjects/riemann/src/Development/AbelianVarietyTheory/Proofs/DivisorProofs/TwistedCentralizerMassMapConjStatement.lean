import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCentralizerMassMapConj
import Development.AbelianVarietyTheory.Definitions.Divisors.PointSide
open GlobalTheory.LKCount
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedCentralizerMass_map_conj : ∀ {G : Type} [Group G] (Γ' T C : Subgroup G) (t : G), t ∈ T → C ≤ T → massC Γ' T (C.map (MulAut.conj t).toMonoidHom) = massC Γ' T C := by
  first | exact @GlobalTheory.LKCount.massC_map_conj | exact GlobalTheory.LKCount.massC_map_conj | (intros; apply GlobalTheory.LKCount.massC_map_conj <;> assumption)
