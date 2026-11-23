import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibrePointField
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecValAt

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_fibre_point_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l' : Level H) (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype) (p : ℕ), p.Prime → (p : ℂ) ∈ W.nonunits → (p : c'.F) ∈ (c'.V W).nonunits → ∀ (A : Type) [CommRing A] [IsDomain A] (ξ : Sp A ⟶ Y.X), ξ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) ∈ Set.range Y.j → ∀ (K : Type) [Field K] (ψ : A →+* K), Function.Injective ψ → ∃ yy : Sp K ⟶ Xo'.XF c', yy ≫ Y.j = spMap ψ ≫ ξ := by
  first | exact @GlobalTheory.FlatModel.GenPt.exists_lift_genericFibre | exact GlobalTheory.FlatModel.GenPt.exists_lift_genericFibre | (intros; apply GlobalTheory.FlatModel.GenPt.exists_lift_genericFibre <;> assumption)
