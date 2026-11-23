import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.AcycSimp
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Faceexact

open NumberField UpperTheory.V

theorem UpperTheory.V.ConeExtensionAcyclic.sx_exact (L : Type) [Field L] [NumberField L] [IsTotallyComplex L] (N m : ℕ) :
    KH.FaceExactTo (KT.Sx L N) (KT.Sx.face L N) m :=
  have h := ConeExtensionAcyclic.acyc_simp (KT.good L N)
  KT.faceexact _ _ h.1 h.2.1 h.2.2 m
