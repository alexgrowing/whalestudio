import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DHRealAdSmul

open NumberField GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.ThetaDecay

def archAt (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) : AF F →+* ℂ :=
  (InfinitePlace.Completion.extensionEmbedding w).comp (evInf F w).toRingHom

def coB (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    Module.Basis (Fin (Module.finrank F E)) (AF F) (AE F E) :=
  Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)

end GlobalTheory.ThetaDecay

end
