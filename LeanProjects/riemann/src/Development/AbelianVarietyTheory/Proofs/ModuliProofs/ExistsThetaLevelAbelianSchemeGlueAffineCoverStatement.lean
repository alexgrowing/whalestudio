import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemeGlueAffineCover
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaLevelAbelianScheme_glue_affineCover : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (m : ℕ) (S : Scheme.{0}) [IsReduced S] (s : S ⟶ Sp o) (I : Type) (R : I → Type) [∀ i, CommRing (R i)] (x : ∀ i, Sp (R i) ⟶ S) (t : ∀ i, TObj g (N' ^ 2) J b (x i ≫ s)), 2 ≤ m → m ^ 2 ∣ N' → Odd N' → (∀ i, IsOpenImmersion (x i)) → (∀ p : S, ∃ i, p ∈ Set.range (x i)) → (∀ i i' (T : Type) [CommRing T] (a : Sp T ⟶ Sp (R i)) (a' : Sp T ⟶ Sp (R i')) (u : TObj g (N' ^ 2) J b (a ≫ x i ≫ s)), IsOpenImmersion a → a ≫ x i = a' ≫ x i' → TMap u (t i) a → TMap u (t i') a') → ∃ t₀ : TObj g (N' ^ 2) J b s, ∀ i, TMap (t i) t₀ (x i) := by
  first | exact @GlobalTheory.ThetaAffineGlue.exists_glue | exact GlobalTheory.ThetaAffineGlue.exists_glue | (intros; apply GlobalTheory.ThetaAffineGlue.exists_glue <;> assumption)
