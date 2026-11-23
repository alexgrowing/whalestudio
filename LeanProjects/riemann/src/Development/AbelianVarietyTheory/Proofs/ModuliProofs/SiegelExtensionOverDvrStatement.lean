import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelExtensionOverDvr
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_extension_over_dvr : Out.Laws → Out.Laws2 → ∀ (g k : ℕ) (J La : Type) [AddCommGroup La] (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] La) (bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] La) (o B : Type) [CommRing o] [CommRing B] (b : TBase o k) (ζ : B) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (β : o →+* V) (s₁ : Sp V ⟶ Sp B) (s' : Sp K ⟶ Sp o) (s₁' : Sp K ⟶ Sp B) (c : SiegPre g k ζ s₁) (c' : SiegPre g k ζ s₁') (t' : TObj g k J b s'), s' = spMap (algebraMap V K) ≫ spMap β → c.Principal → SiegPB c' c (spMap (algebraMap V K)) → TSieg bas bas' t' c' → ∃ t : TObj g k J b (spMap β), TMap t' t (spMap (algebraMap V K)) := by
  first | exact @GlobalTheory.ThetaExtend.exists_tObj_extension | exact GlobalTheory.ThetaExtend.exists_tObj_extension | (intros; apply GlobalTheory.ThetaExtend.exists_tObj_extension <;> assumption)
