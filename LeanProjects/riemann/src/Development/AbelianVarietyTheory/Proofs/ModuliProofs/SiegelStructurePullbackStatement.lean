import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelStructurePullback
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
theorem _root_.GlobalTheory.T.siegel_structure_pullback : ∀ (g k : ℕ) (J La : Type) [AddCommGroup La] (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] La) (bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] La) (o B : Type) [CommRing o] [CommRing B] (b : TBase o k) (ζ : B) (S S' : Scheme.{0}) (s : S ⟶ Sp o) (s₁ : S ⟶ Sp B) (s' : S' ⟶ Sp o) (s₁' : S' ⟶ Sp B) (t : TObj g k J b s) (c : SiegPre g k ζ s₁) (t' : TObj g k J b s') (c' : SiegPre g k ζ s₁') (f : S' ⟶ S), TSieg bas bas' t c → TMap t' t f → (SiegPB c' c f ↔ TSieg bas bas' t' c') := by
  first | exact @GlobalTheory.ZM.siegPB_iff_tSieg | exact GlobalTheory.ZM.siegPB_iff_tSieg | (intros; apply GlobalTheory.ZM.siegPB_iff_tSieg <;> assumption)
