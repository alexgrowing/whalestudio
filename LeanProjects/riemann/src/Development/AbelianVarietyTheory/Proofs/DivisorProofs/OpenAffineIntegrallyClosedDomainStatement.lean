import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OpenAffineIntegrallyClosedDomain
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitChartAt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDiscreteValuationRingAndFiniteResidueFieldValu
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DensityStatementHolds
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsIntegralCoeffZeroMulOfAevalInv

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.open_affine_integrally_closed_domain : ∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) (p : ℕ) [Fact p.Prime], (p : F) ∈ V.nonunits → ∀ (X : Scheme.{0}) (s : X ⟶ Sp V) (Xw : X.Opens), IsIntegral X → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → Flat s → LocallyOfFiniteType s → Xw ≤ X.basicOpen (p : Γ(X, ⊤)) → (Xw : Set X).Nonempty → ∀ (A : Type) [CommRing A] (w : Sp A ⟶ X), IsOpenImmersion w → Nonempty (Sp A) → ∃ (_ : IsDomain A) (_ : IsIntegrallyClosed A) (_ : Algebra V A) (_ : Algebra.FiniteType V A), Function.Injective (algebraMap V A) ∧ ∃ e : A, e ≠ 0 ∧ ∀ (T : CDVR) (kO : T.V →+* 𝓞_ℂ_[p]) (φ : A →+* T.V), T.FinRes → Function.Injective kO → φ e ≠ 0 → IsTest p Xw (spMap (kO.comp φ) ≫ w) := by
  first | exact @GlobalTheory.FlatModel.chart_normal_domain_testPoints | exact GlobalTheory.FlatModel.chart_normal_domain_testPoints | (intros; apply GlobalTheory.FlatModel.chart_normal_domain_testPoints <;> assumption)
