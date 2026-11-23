import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LeftNondeg
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsConn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageCochainExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonSecOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveRootPowUnitSubProdPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BocksteinReductionIsRed
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

noncomputable section

namespace GlobalTheory.EtC.BockRed

open GlobalTheory.EtC

def comp {S R T : Type} [CommRing S] [CommRing R] [CommRing T] {I : Cx S} {J : Cx R} {K : Cx T}
    (ρ : SemiMap I J) (σ : SemiMap J K) : SemiMap I K where
  app U s := (σ.app U s).comp (ρ.app U s)
  nat g s a := by
    change Sec.res g (σ.app _ s (ρ.app _ s a)) = σ.app _ s (ρ.app _ s (Sec.res g a))
    rw [σ.nat, ρ.nat]
  comm U s t a := by
    change Sec.map _ (σ.app U s (ρ.app U s a)) = σ.app U t (ρ.app U t (Sec.map _ a))
    rw [σ.comm, ρ.comm]

end GlobalTheory.EtC.BockRed

end
