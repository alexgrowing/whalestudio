import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.SharpRestriction.ParConsts
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem cc_mul_self (φ : Formalism.HC.Frame) : φ.cc * φ.cc = 1 := by
  ext <;> simp [Formalism.HC.Frame.cc, c0]

theorem hcAt_eq_hc : ∀ (D : D7) (ρ : D.what₂.Tau) (g : D.R.GG), (((D.eTau ρ : D.R.Psi) : D.R.GG) = g ∨ ((D.eTau ρ : D.R.Psi) : D.R.GG) * D.R.cc = g) → hcAt D g = D.hc ρ := by
  intro D ρ g h
  have hm : ((D.eTau ρ : D.R.Psi) : D.R.GG).1.2 = 1 := (Formalism.HC.Frame.mem_Psi_iff _).1 (D.eTau ρ).2
  have hp : plc g = ((D.eTau ρ : D.R.Psi) : D.R.GG) := by
    rcases h with rfl | rfl
    · simp [plc, hm]
    · unfold plc
      have h2 : (((D.eTau ρ : D.R.Psi) : D.R.GG) * D.R.cc).1.2 ≠ 1 := by
        simp [Formalism.HC.Frame.cc, c0, hm]
      rw [if_neg h2, mul_comm, mul_assoc, cc_mul_self, mul_one]
  unfold hcAt
  have : (⟨plc g, plc_mem g⟩ : D.R.Psi) = D.eTau ρ := Subtype.ext hp
  rw [this, Equiv.symm_apply_apply]

end GlobalTheory.HTW.Rec
