import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.ordCount_of :
    OrdDecomp → Telescope → OrdCount := by
  intro hD hT q n P F I _ v hR
  obtain ⟨A, hA, h0, hs⟩ := hD q n P F I v hR
  have key := hT q n P F (fun j => Multiset.map (v j) Finset.univ.val) A hA h0 hs
  simp only [Multiset.map_map] at key
  exact key
