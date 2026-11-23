import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsGal

noncomputable section

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace Formalism.L2

structure OmFrame (D : D7) where

  jE : D.host.E →+* AlgebraicClosure ℚ

  eOm : D.nd.Om ≃+* AlgebraicClosure ℚ
  comm : ∀ x : D.host.E, eOm (algebraMap D.host.E D.nd.Om x) = jE x

structure LPTiedPlaceholder (D : D7) : Type

end Formalism.L2
