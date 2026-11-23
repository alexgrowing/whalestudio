import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyAllIff
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.HeightCounting

theorem omFrame_exists_with_jE (D : D7) (jE : D.host.E →+* Qb) : ∃ fr : OmFrame D, fr.jE = jE := by
  letI : Algebra D.host.E Qb := jE.toAlgebra
  haveI : Algebra.IsAlgebraic ℚ Qb := inferInstance
  haveI : IsScalarTower ℚ D.host.E Qb := .of_algebraMap_eq fun x => (map_ratCast jE x).symm
  haveI : Algebra.IsAlgebraic D.host.E Qb := .tower_top (K := ℚ) D.host.E
  haveI : IsAlgClosure D.host.E Qb := ⟨inferInstance, inferInstance⟩
  let e : D.nd.Om ≃ₐ[D.host.E] Qb := IsAlgClosure.equiv D.host.E D.nd.Om Qb
  exact ⟨⟨jE, e.toRingEquiv, fun x => e.commutes x⟩, rfl⟩

end GlobalTheory.HeightCounting
