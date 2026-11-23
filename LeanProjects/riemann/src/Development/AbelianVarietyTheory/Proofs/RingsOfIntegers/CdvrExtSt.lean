import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FinExtIn
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsCdvrFiniteExtension

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PlaceExtField

theorem cdvrExtSt : PullbackSections.CDVRExtSt := by
  intro T hT K _ jK hfin
  letI := jK.toAlgebra
  obtain ⟨T', iT, e, ψ, _, he, hv, hψ, _, hres⟩ := exists_cdvr_finite_extension T K
  refine ⟨T', ψ.toRingHom, e, he, fun a _ => ?_, hres hT⟩

  have h : ψ.toRingHom (jK a) = iT a := hψ a
  rw [h, hv a]

end GlobalTheory.PlaceExtField
