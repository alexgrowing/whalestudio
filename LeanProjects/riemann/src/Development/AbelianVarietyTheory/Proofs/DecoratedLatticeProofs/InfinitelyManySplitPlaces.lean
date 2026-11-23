import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair ValuativeRel NumberField Filter
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl

theorem infinite_splitIdem_places (D : D7) :
    {v : Pl D | ∃ (e : AE D) (ε : AF D.host.F), IsSplitIdem D e ∧ IsPlaceIdem D v ε ∧
      e + cA D e = algebraMap (AF D.host.F) (AE D) ε}.Infinite := by
  intro hf
  obtain ⟨v, hv, ⟨τ⟩⟩ := GlobalTheory.Orb.exists_split_place_notMem (GlobalTheory.AdelicU.isCMExt_host D) hf.toFinset
  have he := GlobalTheory.AdelicU.Supp.splitAt_splitIdemAd (D := D) τ
  have hε := GlobalTheory.AdelicU.Supp.isPlaceIdem_placeIdem D v
  have hs := he.2.2.trans (GlobalTheory.AdelicU.Supp.pl_eq D v)
  exact hv (hf.mem_toFinset.2 ⟨_, _, ⟨he.1, he.2.1, v, _, hε, hs⟩, hε, hs⟩)

end GlobalTheory.FinPl
