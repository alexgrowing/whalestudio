import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChangeLifts.SplitLift
import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChange.ConjIsoOf
import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChange.PBasic
import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChange.PSIsoSat
import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChange.PSTwSat
import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChange.P_SSatEx
import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChange.PSSmo
import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChange.PSConjSpaceC
import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChange.PSConjSpaceR
import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChange.PSConjSatC
import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChange.PSConjSatR
import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChange.PSNormPow
import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChange.PSGalAdEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.StrongMultOneReal
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.NormQuad
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.SelfIso

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Published

namespace UpperTheory.CBC

private theorem not_real_complex (F : Type) [Field F] [NumberField F] (h : IsTotallyReal F) (h' : IsTotallyComplex F) : False := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
  exact (InfinitePlace.not_isReal_iff_isComplex.2 (h'.isComplex v)) (h.isReal v)

end UpperTheory.CBC
