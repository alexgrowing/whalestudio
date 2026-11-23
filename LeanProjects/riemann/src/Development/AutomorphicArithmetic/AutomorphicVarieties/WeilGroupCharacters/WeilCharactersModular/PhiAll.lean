import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ChebotarevFamilies.PhiDec
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ChebotarevFamilies.PhiGS
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.PhiSub
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.W

theorem UpperTheory.V.W.phiAll :
    Pa.CohP → PhiAll := by
  intro hP l _ L Ω _ _ _ _ _ _ s V
  have h := Pa.phiGS hP.gf l L Ω s V
  exact ⟨h, Pa.Det.phiSub l V.frame.η.ker V.frame.η_open h,
    fun v => Pa.phiDec hP.lf l L Ω (s.A v.1) (s.w v.1) (s.hw v.1)⟩
