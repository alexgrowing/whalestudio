import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticCurveSubbundleCover
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppInjectiveOfFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeOfIsOpenImmersion
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithmetic_curve_subbundle_cover : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (E : X.Modules) (r : ℕ), IsArithVar p 1 → IsVB E (r + 1) → ∃ (Y : Scheme.{0}) (ρ : Y ⟶ X) (K : Y.Modules) (i : K ⟶ (Scheme.Modules.pullback ρ).obj E), IsArithVar (ρ ≫ p) 1 ∧ (∀ [IsIntegral Y] [IsIntegral X], ρ (genericPoint Y) = genericPoint X ∧ ρ.residueDegree (genericPoint Y) ≠ 0) ∧ IsSubbundle i ∧ IsVB K r := by
  first | exact @GlobalTheory.CorankOne.exists_modification_subbundle_surface | exact GlobalTheory.CorankOne.exists_modification_subbundle_surface | (intros; apply GlobalTheory.CorankOne.exists_modification_subbundle_surface <;> assumption)
