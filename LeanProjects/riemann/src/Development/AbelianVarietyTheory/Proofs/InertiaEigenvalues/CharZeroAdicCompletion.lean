import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.LocDict

namespace GlobalTheory.LTRecip

instance charZero_adicCompletion (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) :
    CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective

instance isSepClosure_kbar (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) :
    IsSepClosure (w.adicCompletion E) (Kbar w) := inferInstance

end GlobalTheory.LTRecip

end
