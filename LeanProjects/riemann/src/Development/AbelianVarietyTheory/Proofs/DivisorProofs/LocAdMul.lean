import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSkewSignature
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockEmb

noncomputable section

namespace GlobalTheory.UnipEmb

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU
open scoped TensorProduct

variable (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]

def locAd (v : HeightOneSpectrum (𝓞 F)) : Fv F v →ₗ[F] AF F := LinearMap.inr F (Ainf F) (Af F) ∘ₗ singleFin v

theorem locAd_mul (v : HeightOneSpectrum (𝓞 F)) (a b : Fv F v) : locAd F v (a * b) = locAd F v a * locAd F v b :=
  Prod.ext (mul_zero _).symm (singleFin_mul v a b)

def locInc (v : HeightOneSpectrum (𝓞 F)) : Fv F v ⊗[F] E →ₙ+* AF F ⊗[F] E :=
  GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU (locAd F v) (locAd_mul F v)

end GlobalTheory.UnipEmb

end
