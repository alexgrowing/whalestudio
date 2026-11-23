import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SerreVanishingLineBundleInvMixFixedDifference
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Tri
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AmpleGen
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.serre_vanishing_lineBundleInvMix_fixed_difference : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → Out.RelAmple A L → ∀ d : ℤ, ∃ N : ℕ, ∀ a b : ℕ, N ≤ a + b → (a : ℤ) - b = d → ∀ j : ℕ, ¬ NV A (mix A L a b) (j + 1) := by
  first | exact @GlobalTheory.AmpleGen.exists_not_NV_mix | exact GlobalTheory.AmpleGen.exists_not_NV_mix | (intros; apply GlobalTheory.AmpleGen.exists_not_NV_mix <;> assumption)
