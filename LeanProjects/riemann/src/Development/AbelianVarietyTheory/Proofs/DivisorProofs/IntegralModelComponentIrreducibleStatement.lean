import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelComponentIrreducible
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.MemRangeOfIsAlgebraicRatFun
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_model_component_irreducible : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l' : Level H) (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype)
    (p : ℕ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ U : (Xo'.XF c').Opens,
    (∀ (k : Type) [Field k] (f : c'.F →+* k),
      IrreducibleSpace ↑(pullback (U.ι ≫ pullback.snd Xo'.s (spMap (IntermediateField.inclusion c'.le).toRingHom)) (spMap f))) →
    ∃ Xw : Y.X.Opens, (Xw : Set Y.X) ⊆ Set.range Y.j ∧ Xw ≤ Y.X.basicOpen (p : Γ(Y.X, ⊤)) ∧
      (∀ z, Y.j z ∈ Xw ↔ z ∈ U) ∧ GeomIrr Y.s Xw := by
  first | exact @GlobalTheory.FlatModel.ModelOpen.exists_geomIrr_open | exact GlobalTheory.FlatModel.ModelOpen.exists_geomIrr_open | (intros; apply GlobalTheory.FlatModel.ModelOpen.exists_geomIrr_open <;> assumption)
