import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.DescentStatement

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.DescPf

open scoped TensorProduct
open Module

variable {F F' V : Type} [Field F] [Field F'] [Algebra F F'] [AddCommGroup V] [Module F V]

theorem indep_iff {ι : Type} (v : ι → V) :
    LinearIndependent F v ↔ LinearIndependent F' (fun i => (1 : F') ⊗ₜ[F] v i) := by
  constructor
  · intro hv
    exact Module.Flat.linearIndependent_one_tmul hv
  · intro h
    have h' : LinearIndependent F (fun i => (1 : F') ⊗ₜ[F] v i) :=
      h.restrict_scalars' F
    exact LinearIndependent.of_comp (TensorProduct.mk F F' V 1) h'

end ReciprocityTheory.ChartRestriction.G.AR.Up.DescPf

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

end ReciprocityTheory.ChartRestriction.G.AR.Up
