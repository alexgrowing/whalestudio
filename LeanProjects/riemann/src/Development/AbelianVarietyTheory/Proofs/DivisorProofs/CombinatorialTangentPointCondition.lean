import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducesPl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSectionFrameInvariance
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeExistsUniqueOfSamePoint
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsCombAtGMulVec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValueStatementHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalFlagPointTangentDualNumber

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open scoped NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.FlatModel GlobalTheory.Toroidal
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.VertForm
open GlobalTheory.DetHT
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.ShFam.Descent

namespace GlobalTheory.FramedPointCoeffs

open ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj MonObj

theorem coeffs_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F)
    (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (S : Type) [Field S] [Algebra c.F S] (P : FrPt Xo c S) (σ : E →+* ℂ)
    (a a' : Fin (Dw.mult σ) → S) (w : Sp (DualNumber S) ⟶ Z.t.G.left),
    IsCombAtG Z.t (GlobalTheory.AllWt.ptF P ≫ Z.j) ((frameOf Z P).v σ) a w →
    IsCombAtG Z.t (GlobalTheory.AllWt.ptF P ≫ Z.j) ((frameOf Z P).v σ) a' w → a = a' := by
  intro E _ _ _ H Dw l Xo c O _ β Z S _ _ P σ a a' w ha ha'
  have hw : Formalism.L2.Pj.IsTanAtG Z.t (GlobalTheory.AllWt.ptF P ≫ Z.j) w :=
    GlobalTheory.ShFam.Pad.Guard.comb_tan ((frameOf Z P).tan σ) ha
  have hv : ∀ i, IsEigV (actR (x0 := GlobalTheory.AllWt.ptF P ≫ Z.j) (S := S) Z.t.act) (embK c σ)
      (GlobalTheory.EigLetters.tvG ((frameOf Z P).tan σ i)) := by
    intro i b
    apply tanM_ext
    apply Over.OverMorphism.ext
    exact (frameOf Z P).eig σ i b
  have h1 := (GlobalTheory.EigLetters.combG_iff ((frameOf Z P).v σ) ((frameOf Z P).tan σ) a hw).1 ha
  have h2 : IsEigV (actR (x0 := GlobalTheory.AllWt.ptF P ≫ Z.j) (S := S) Z.t.act) (embK c σ)
      (GlobalTheory.EigLetters.tvG hw) := by
    rw [h1]
    exact GlobalTheory.EigLetters.eig_combG σ _ hv a
  have he : ∀ b : 𝓞 E, w ≫ (Z.t.act.act b).left =
      spMap (epsMul (algebraMap c.F S (embK c σ b))) ≫ w := by
    intro b
    exact congrArg (fun V => (tv V).left) (h2 b)
  exact ((frameOf Z P).basis σ w hw he).unique ha ha'

end GlobalTheory.FramedPointCoeffs
