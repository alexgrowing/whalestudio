import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKaehlerBasisDifferentialsOfTopFormFrame
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBaseFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitMkOfFormallyUnramified
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_kaehlerBasis_differentials_of_topFormFrame : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (m : ℕ), SmoothOfRelativeDimension m p → ∀ (U : X.Opens) (x : Fin m → Γ(X, U)), GlobalTheory.TopForm.IsFrame (GlobalTheory.TopForm.dOn p x) → ∃ b : Module.Basis (Fin m) Γ(X, U) (GlobalTheory.TopForm.Omega (algX p U)), ∀ i, b i = GlobalTheory.TopForm.dFun (algX p U) (x i) := by
  first | exact @GlobalTheory.TopForm.FrameBasis.exists_basis_of_isFrame | exact GlobalTheory.TopForm.FrameBasis.exists_basis_of_isFrame | (intros; apply GlobalTheory.TopForm.FrameBasis.exists_basis_of_isFrame <;> assumption)
