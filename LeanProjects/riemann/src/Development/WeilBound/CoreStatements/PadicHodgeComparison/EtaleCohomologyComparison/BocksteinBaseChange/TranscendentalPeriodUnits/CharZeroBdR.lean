import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.TranscendentalPeriodUnits.CrystallineSemistableComparison
import GroundTheory.PAdicHodge.WAFracB

set_option backward.isDefEq.respectTransparency false

noncomputable section

open Formalism.Per6 GroundTheory.PAdicHodge DeRhamPotentiallySemistable.DRPst

namespace CrystallineSemistableComparison

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

instance charZero_bdR : CharZero (BdR l) := ⟨fun a b h => by
  have : qQ l (a : ℚ_[l]) = qQ l (b : ℚ_[l]) := by rw [map_natCast, map_natCast]; exact h
  exact Nat.cast_injective ((qQ l).injective this)⟩

variable (l) in

abbrev Fr : Subfield (BdR l) :=
  ACris.fracBCris (untilt_epsilon (p := l)) untilt_frobeniusEquiv_symm_epsilon_ne_one

def cK (g : K.fixingSubgroup) : BdR l := qQ l (period_ring_base.κ g.1) * tQ l

theorem σ_uQ (g : K.fixingSubgroup) : σD g.1 (uQ l) = uQ l + cK g := (period_ring_base.base l).σ_u g.1

end CrystallineSemistableComparison
