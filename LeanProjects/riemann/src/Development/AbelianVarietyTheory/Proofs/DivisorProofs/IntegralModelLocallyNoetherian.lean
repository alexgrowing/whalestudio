import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTangentPresentationPrime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationSubringDedekindOpenImmersion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.ModelNoeth

theorem isLocallyNoetherian_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l' : Level H)
    (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype) (p : ℕ),
    p.Prime → (p : ℂ) ∈ W.nonunits → IsLocallyNoetherian Y.X := by
  intro E _ _ _ H Dw l' Xo' c' W Y p _ _
  obtain ⟨⟨_, hD⟩, -, -⟩ :=
    (GlobalTheory.CoeffValuation.isDedFrac_and_isOpenImmersion E H l' c' (c'.V W)).1
  haveI : IsNoetherianRing (c'.V W) := hD.toIsNoetherian
  obtain ⟨N, i, hi, hcomp⟩ := Y.proj
  haveI := hi
  haveI := isProper_str (c'.V W) N
  haveI : LocallyOfFiniteType (i ≫ PSpace.str (c'.V W) N) := inferInstance
  haveI : LocallyOfFiniteType Y.s := hcomp ▸ this
  exact LocallyOfFiniteType.isLocallyNoetherian Y.s

end GlobalTheory.ModelNoeth
