import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.OrbAddUp
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.OrbAddOne
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.OrbRestr
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.OrbRestrOne
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.EntAtD
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SumOrbC
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.OrbBoundF
import Formalism.SharpRestriction.Divisibility.OrbitPlaces
import Development.AutomorphicArithmetic.OrbitLabellings.KvalGeThetaOfShape
import Development.AutomorphicArithmetic.OrbitLabellings.FInertSubEatILeOrbitAverageSubErrors

namespace Formalism.MainNotions.DIV.Lemmas.OrbitEntryBounds

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.OrbitPlaces

def toEnt {D : D7} (E : OrbitPlaces.Ent D) : PI.OrbJet.Ent D :=
  ⟨E.nu, E.nu_row, E.nu_rows, E.Th, E.ep, E.be, E.sg⟩

theorem addition_bound_holds (D : D7) (E : OrbitPlaces.Ent D) : OrbitPlaces.OrbitsAddLowerBound E := by
  intro p _ h u i hi R hR ep sg be hbe β hβ Th hTh
  exact PI.OrbAddUp D (toEnt E) p ⟨h.five, h.even, h.two⟩ u i hi R hR ep sg be hbe β hβ Th hTh

theorem orbitsAddAtConjugate_ent (D : D7) (E : OrbitPlaces.Ent D) : OrbitPlaces.OrbitsAddAtConjugate E :=
  PI.OrbAddOne D (toEnt E)

theorem restriction_bound_holds (D : D7) (E : OrbitPlaces.Ent D) : OrbitPlaces.OrbitRestriction E := by
  intro p _ h u i R hR ep sg be hbe Th hTh r hr
  exact PI.OrbRestr D (toEnt E) p ⟨h.five, h.even, h.two⟩ u i R hR ep sg be hbe Th hTh r hr

theorem orbit_restriction_at_conjugate (D : D7) (E : OrbitPlaces.Ent D) : OrbitPlaces.OrbitRestrictionAtConjugate E :=
  PI.OrbRestrOne D (toEnt E)

theorem entry_divisor_bound_holds (D : D7) (E : OrbitPlaces.Ent D) (Dx : DivX D) (hs : OrbitPlaces.ThetaKernelShapeAtD E Dx) : OrbitPlaces.EntriesAtDiscriminant E Dx := by
  intro u μ w hL hc i hi L L'
  exact _root_.jet_bound_ramified_prime D Dx E.nu E.nu_row E.nu_rows E.Th hs u μ w hL hc i hi L L'

private theorem entry_number_bound_holds (D : D7) (L : SizeData₂ D) (X : Inst D L) (K : Consts) (E : OrbitPlaces.Ent D) (ce : ErrC) (C6 C : ℝ)
    (hS : OrbitPlaces.Shape D L X E) (hC : OrbitPlaces.CLarge C6 C K ce) : OrbitPlaces.ScaledGeneratorsInSup E L K ce := by
  intro p hp h5 hcs hpX u i hi
  exact ⟨fun Th hTh => UpperTheory.kvalGe_theta_of_shape D L X E hS p h5 hcs.1 hcs.2.2 hpX u i hi Th hTh,
    fun hL => UpperTheory.fInert_sub_eatI_le_orbit_average_sub_errors D L X K E ce C6 C hS hC hL p hp.out h5 hcs hpX i hi⟩

theorem orbit_entry_bounds_of_family (D : D7) (L : SizeData₂ D) (X : Inst D L) (K : Consts) (Dx : DivX D) (E : OrbitPlaces.Ent D) (ce : ErrC) (C6 C : ℝ)
    (hF : OrbitPlaces.OrbitValuationBound E X K ce) (hs : OrbitPlaces.ThetaKernelShapeAtD E Dx) (hS : OrbitPlaces.Shape D L X E) (hC : OrbitPlaces.CLarge C6 C K ce) :
    OrbitPlaces.Core D L X K Dx E ce C :=
  ⟨addition_bound_holds D E, orbitsAddAtConjugate_ent D E, restriction_bound_holds D E, orbit_restriction_at_conjugate D E, hF, entry_divisor_bound_holds D E Dx hs,
    PI.SumOrbC D L X K ce E C6 C hS hC, entry_number_bound_holds D L X K E ce C6 C hS hC⟩

theorem orbit_entry_bounds_hold (D : D7) (L : SizeData₂ D) (X : Inst D L) (K : Consts) (Dx : DivX D) (E : OrbitPlaces.Ent D) (ce : ErrC) (C6 C : ℝ)
    (hA : OrbitPlaces.OrbitLetterBoundsAll C6 C) (hs : OrbitPlaces.ThetaKernelShapeAtD E Dx) (hS : OrbitPlaces.Shape D L X E) (hC : OrbitPlaces.CLarge C6 C K ce) :
    OrbitPlaces.Core D L X K Dx E ce C :=
  orbit_entry_bounds_of_family D L X K Dx E ce C6 C (PI.OrbBoundF D L X K ce E C6 C hA hS hC) hs hS hC

end Formalism.MainNotions.DIV.Lemmas.OrbitEntryBounds
