import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IteratedLiftChains
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormSatakeLeOfUnitarySphericalGLStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PowDvdOfHermMatEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SatakeParameterGLStarEqInvOfUnitarisable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeActsByScalarCommutative
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenIsCompactUnitaryIntegralPoints

noncomputable section

open NumberField IsDedekindDomain Formalism.UG GlobalTheory.PRep GlobalTheory.LFun GlobalTheory.LFun.HeckeScalar

namespace GlobalTheory.LFun.IsoBound

section General

variable {G H : Type} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ρ : Representation ℂ G H}
  {K : Subgroup G} {x : H}

def gen (hx : x ∈ fixed ρ K) : Representation ℂ G (LinearMap.range (orbitMap ρ K x)) :=
  sub ρ _ (by
    rintro g _ ⟨φ, rfl⟩
    exact ⟨_, orbitMap_permRep hx g φ⟩)

end General

end GlobalTheory.LFun.IsoBound

end
