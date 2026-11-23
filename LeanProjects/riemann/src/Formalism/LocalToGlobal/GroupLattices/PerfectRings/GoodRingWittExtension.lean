import Formalism.SharpRestriction.GrowthBounds.ObjBridge
import Formalism.LocalToGlobal.GroupLattices.PerfectRings.JOInjective

noncomputable section

namespace Formalism.L2.G

open Formalism.MainNotions.G

variable (p : ℕ) [hp : Fact p.Prime] (n : ℕ)

def dvrOO (h5 : 5 ≤ p) (h2 : 2 ≤ n) (he : Even n) : UniformizedDVR p (OO p n) :=
  dvrOfStd (settingStd p n h5 h2 he)

def resF : F1 p n →+* FF (OO p n) :=
  (Ideal.Quotient.lift (Ideal.span {(p : WQ p n)})
      ((IsLocalRing.residue (OO p n)).comp (jO p n)) (by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [RingHom.comp_apply, map_mul, map_mul, map_natCast, ← wU_sq, map_pow]
    have : IsLocalRing.residue (OO p n) (wU p n) = 0 := by
      rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact (Formalism.BasicNotions.Examples₂.GatR.om_irreducible (WittVector.irreducible p)).not_isUnit
    rw [this]; simp)).comp
    (WittVector.quotientPEquiv (p := p) (k := F1 p n)).symm.toRingHom

end Formalism.L2.G
