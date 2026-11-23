import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Statements

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory IsDedekindDomain
open scoped Pointwise ComplexOrder ENNReal NumberField.AdeleRing

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def adeleSplit (h : HermitianForm F E W) (v : Basis ι E W) :
    unitaryPoints F E (gram h.toSesq v) 𝔸[F] ≃ₜ*
      unitaryPoints F E (gram h.toSesq v) (InfiniteAdeleRing F) ×
        unitaryPoints F E (gram h.toSesq v) (FiniteAdeleRing (𝓞 F) F) :=
  (unitaryCongr (gram h.toSesq v) (adeleRingEquivProd F) (by exact continuous_id)
      (by exact continuous_id)).trans
    (unitaryProdEquiv F (gram h.toSesq v) _ _ (isUnit_det_gram h v))

def ArchimedeanUnitaryEquiv.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∃ ψ : unitaryPoints F E (gram h.toSesq v) (InfiniteAdeleRing F) ≃ₜ* archUnitary h v,
    ∀ γ : h.unitaryGroup, ψ (adeleSplit h v (hermitianDiagonal h v γ)).1 = archEmbed h v γ

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
