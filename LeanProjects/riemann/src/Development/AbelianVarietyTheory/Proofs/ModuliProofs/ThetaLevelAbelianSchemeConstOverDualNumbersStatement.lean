import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelAbelianSchemeConstOverDualNumbers
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
theorem _root_.GlobalTheory.T.thetaLevelAbelianScheme_const_over_dualNumbers : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (w w' : J) (K : Type) [Field K] (s : Sp (DualNumber K) ⟶ Sp o) (s₀ : Sp K ⟶ Sp o) (t : TObj g k J b s) (t₀ : TObj g k J b s₀) (io : t₀.A.left ⟶ t.A.left) (ψ₀ : t.A.left ⟶ t₀.A.left), t.Prim w w' → IsGrpPullback t₀.A t.A (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) io → LBIso t₀.L (t.L.pull io) → (∀ i, (t₀.pt i).left ≫ io = spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ (t.pt i).left) → (∀ j, (t₀.act j).left ≫ io = io ≫ (t.act j).left) → IsGrpPullback t.A t₀.A (spMap (algebraMap K (DualNumber K))) ψ₀ → io ≫ ψ₀ = 𝟙 _ → TMap t t₀ (spMap (algebraMap K (DualNumber K))) := by
  first | exact @GlobalTheory.ConstTheta.tMap_of_const | exact GlobalTheory.ConstTheta.tMap_of_const | (intros; apply GlobalTheory.ConstTheta.tMap_of_const <;> assumption)
