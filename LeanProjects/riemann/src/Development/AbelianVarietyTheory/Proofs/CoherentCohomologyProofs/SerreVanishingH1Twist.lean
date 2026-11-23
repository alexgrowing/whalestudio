import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsFiniteGradedModuleLineBundleSectionsStatement
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CubeComplexGradedModuleExactAtOfLargeDegree
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.FirstCohomologyVanishesOfExactSecCube

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.AbLaw

theorem exists_h1Zero_tw_of_veryAmpleBy (R : Type) [CommRing R] (Y : Scheme.{0})
    (f : Y ⟶ Spec (CommRingCat.of R)) [IsNoetherianRing R] (H : LB Y) (m : ℕ)
    (s : Fin (m + 1) → LB.Sec H) (M : LB Y) (hH : H.IsLB) (hM : M.IsLB)
    (hs : VeryAmpleBy f H s) : ∃ t₀ : ℤ, ∀ t, t₀ ≤ t → FirstCohomologyVanishes (tw M H t) := by
  obtain ⟨N, _, _, _, _, 𝒩, _, _, hN, hφ⟩ := GlobalTheory.T.exists_finite_gradedModule_lineBundleSections R Y f H m s M hH hM hs
  obtain ⟨t₀, ht₀⟩ := GlobalTheory.cubeComplex_grCube_exactAt_of_finite (Fin (m + 1)) R N 𝒩 hN
  refine ⟨t₀, fun t ht => ?_⟩
  obtain ⟨φ, hφ⟩ := hφ t
  have := isIso_cechComplexMap φ hφ
  have h1 := (cechComplex_exactAt_succ_iff_cube _ 0).2 (ht₀ t ht 2)
  have h2 := h1.of_iso (asIso (cechComplexMap φ))
  exact firstCohomologyVanishes_of_exact_secCube R Y f (tw M H t) (Fin (m + 1)) (fun i => nonzeroLocus (s i))
    (isLB_tw hM hH t) hs.1 (fun i => (hs.2 i).1) ((cechComplex_exactAt_succ_iff _ 0).1 h2)

end GlobalTheory.AbLaw
