import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrallyClosedPointLevelExtends
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTangentPresentationPrime

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

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrally_closed_point_level_extends : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l' : Level H)
    (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype) (p : ℕ)
    [Fact p.Prime] (n : ℕ), (p : ℂ) ∈ W.nonunits → l'.A = p ^ n →
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (ξ : Sp R ⟶ Y.X)
      (y : Sp (FractionRing R) ⟶ Xo'.XF c'), spMap (algebraMap R (FractionRing R)) ≫ ξ = y ≫ Y.j → ∀ (a : Dw.La)
      (κ : (Sp (FractionRing R) ⟶ Y.t.G.left) → Rˣ),
      (∀ (e σ : Over.mk y ⟶ Y.oF.t.G), e.left = y ≫ (Y.oF.etaA a).left → σ ^ (p ^ n) = 1 →
        Out.WeilIs Y.oF.t.G Y.oF.t.PP.L ((p ^ n : ℕ) : ℤ) e σ
          (unitOn (Units.map (algebraMap R (FractionRing R)).toMonoidHom (κ (σ.left ≫ Y.m.φ))))) →
    ∀ (f : R) (wf : Over.mk (spMap (algebraMap R (Localization.Away f)) ≫ ξ) ⟶ Y.t.G), wf ^ (p ^ n) = 1 →
    ∀ (g : Localization.Away f →+* FractionRing R), g.comp (algebraMap R _) = algebraMap R (FractionRing R) →
    ∀ (x0 : R →+* 𝓞_ℂ_[p]) (φ : Localization.Away f →+* ℂ_[p]),
      φ.comp (algebraMap R _) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp x0 →
    ∀ (yy : Sp ℂ_[p] ⟶ Xo'.XF c'), spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ spMap x0 ≫ ξ = yy ≫ Y.j →
    ∀ (e σ : Over.mk yy ⟶ Y.oF.t.G), e.left = yy ≫ (Y.oF.etaA a).left → σ.left ≫ Y.m.φ = spMap φ ≫ wf.left →
      σ ^ (p ^ n) = 1 ∧ Out.WeilIs Y.oF.t.G Y.oF.t.PP.L ((p ^ n : ℕ) : ℤ) e σ
        (unitOn (Units.map ((algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp x0).toMonoidHom (κ (spMap g ≫ wf.left)))) := by
  first | exact @GlobalTheory.WeilSpec.weil_spec | exact GlobalTheory.WeilSpec.weil_spec | (intros; apply GlobalTheory.WeilSpec.weil_spec <;> assumption)
