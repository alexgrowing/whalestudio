import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TypedLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocalAdditiveCharContinuous

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.HostUnramP

open NumberField IsDedekindDomain Formalism.BasicNotions

def HostUnramG : Prop :=
  ∀ D : D7, Formalism.L2.SG.Pf.LocCP.LocTied D → ∀ (p : HeightOneSpectrum (𝓞 D.host.F)) (i : Fin 2),
    ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal → ((D.host.g i : ℕ) : 𝓞 D.host.F) ∉ p.asIdeal ^ 2

theorem gi_val (D : D7) (p : HeightOneSpectrum (𝓞 D.host.F)) (i : Fin 2)
    (hi : ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal) :
    p.intValuation ((D.host.g i : ℕ) : 𝓞 D.host.F) = WithZero.exp (-1 : ℤ) := by
  exact Formalism.L2.SG.Pf.TypedLoc.tower_val D.host.F D.host.E (D.host.g_prime i) (D.nd.g_split i) p hi

theorem hostUnramG : HostUnramG := by
  intro D _ p i hi hsq
  have h2 := (p.intValuation_le_pow_iff_mem _ 2).mpr hsq
  rw [gi_val D p i hi] at h2
  have h3 := WithZero.exp_le_exp.mp h2
  omega

end Formalism.L2.SG.Pf.HostUnramP
