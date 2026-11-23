import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualOrbitPageWordBoxStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CloudLowJumpsReflectAndCardStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardSmallTwistedDualJumpsEqRankStatement

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem twistedDualPageWord_small_jumps_card : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ φ : D.R.GG), Roomy L C → (pageWord L j ε τ φ).T2 ∧ ∀ i, ((pageWord L j ε τ φ).J2 i).card = D.R.r ∧ (((pageWord L j ε τ φ).J2 i).filter fun u : ℤ => |u| ≤ (etaHat L : ℤ)).card = D.R.m := by
  intro D L C j ε τ φ hR
  have hbox := (GlobalTheory.T.twistedDualOrbitPageWord_box L C j ε τ φ hR).2.2.2.2.2
  have hcount : ∀ i, (((pageWord L j ε τ φ).J2 i).filter
      fun u : ℤ => |u| ≤ (etaHat L : ℤ)).card = D.R.m := by
    intro i
    refine GlobalTheory.T.card_filter_abs_le_jT2_eq_rank (hcAt D (letter τ φ i)) j (pos ε (letter τ φ i)) L.etaSz ?_ ?_ (hbox i)
    · intro a
      have h := (L.cloud_v (D.eTau.symm ⟨plc (letter τ φ i), plc_mem _⟩) a).1
      exact_mod_cast h
    · intro a
      exact L.be_close _ a j
  refine ⟨fun i => ⟨fun u hu => ?_, (hcount i).le⟩, fun i => ⟨?_, hcount i⟩⟩
  · exact Multiset.mem_of_le
      ((GlobalTheory.T.cloudLowJumps_reflect_and_card (hcAt D (letter τ φ i)) j).2 (pos ε (letter τ φ i))).2.2.2 hu
  · exact ((GlobalTheory.T.cloudLowJumps_reflect_and_card (hcAt D (letter τ φ i)) j).2 (pos ε (letter τ φ i))).2.2.1

end GlobalTheory.HTW
