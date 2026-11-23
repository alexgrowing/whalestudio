import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthGeThreeFiniteEtalePuncturedRegular
import Mathlib
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ModDepthGE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PurityFree
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.depth_ge_three_finite_etale_punctured_regular : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R], IsAdicComplete (maximalIdeal R) R → 3 ≤ ringKrullDim R → ∀ f ∈ maximalIdeal R, f ∉ maximalIdeal R ^ 2 → ∀ [IsLocalRing (R ⧸ Ideal.span {f})], GlobalTheory.PurityFree (R ⧸ Ideal.span {f}) → ∀ (A : Type) [CommRing A] [Algebra R A] [Module.Finite R A], ReciprocityTheory.CA.ModDepthGE R A 2 → (∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R → Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) → ReciprocityTheory.CA.ModDepthGE R A 3 := by
  first | exact @GlobalTheory.LocalLefschetz.depth_three | exact GlobalTheory.LocalLefschetz.depth_three | (intros; apply GlobalTheory.LocalLefschetz.depth_three <;> assumption)
