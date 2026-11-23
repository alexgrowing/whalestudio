import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.VecCoord

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open GlobalTheory.LFun (KGL)
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct Classical

namespace UpperTheory.Gal.W2.Seed

theorem pEvEx : EvEx := by
  intro p E _ _ _ T w hw
  have hk : RingHom.ker T.Φ ≤ RingHom.ker (pLoc E w) := by
    intro x hx
    exact RingHom.mem_ker.2 (((T.Φ_ker x).1 (RingHom.mem_ker.1 hx)) w hw)
  refine ⟨RingHom.liftOfSurjective T.Φ T.Φ_surj ⟨pLoc E w, hk⟩, fun x => ?_⟩
  exact RingHom.liftOfRightInverse_comp_apply _ _ _ ⟨pLoc E w, hk⟩ x

end UpperTheory.Gal.W2.Seed
