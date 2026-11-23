import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PAdicPointPairingCompatible
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.p_adic_point_pairing_compatible : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (p : ℕ) [Fact p.Prime]
    [StarRing (𝓞 E)] (l' : Level H) (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (yb : Sp 𝓞_ℂ_[p] ⟶ Y.X) (yy : Sp ℂ_[p] ⟶ Xo'.XF c') (P : PtP E p)
    (π : P.G.left ⟶ Y.t.G.left) (ψ : P.A.A.left ⟶ Y.oF.t.G.left), PtOn Y yb yy P π ψ →
    (∀ u : Sp (DualNumber 𝓞_ℂ_[p]) ⟶ Y.t.G.left, IsTanAtG Y.t yb u → ∃! x : LieG P.Gt, ITie P π x u) ∧
    (∀ x : LieG P.Gt, ∃ u, IsTanAtG Y.t yb u ∧ ITie P π x u) ∧
    (∀ (m : ℕ) (v : Fin m → (Sp (DualNumber 𝓞_ℂ_[p]) ⟶ Y.t.G.left)) (xs : Fin m → LieG P.Gt) (cf : Fin m → 𝓞_ℂ_[p])
      (u : Sp (DualNumber 𝓞_ℂ_[p]) ⟶ Y.t.G.left) (x : LieG P.Gt), (∀ i, IsTanAtG Y.t yb (v i)) →
      (∀ i, ITie P π (xs i) (v i)) → IsCombAtG Y.t yb v cf u → ITie P π x u →
      P.bLie x = ∑ i, (cf i : ℂ_[p]) • P.bLie (xs i)) ∧
    ∀ (σ : 𝓞 E →+* 𝓞_ℂ_[p]) (x : LieG P.Gt) (u : Sp (DualNumber 𝓞_ℂ_[p]) ⟶ Y.t.G.left), IsTanAtG Y.t yb u →
      ITie P π x u → (IsEigG Y.t σ u ↔ AvDefs.IsEig P.Gt P.oGt σ x) := by
  first | exact @GlobalTheory.FlatModel.tanTie | exact GlobalTheory.FlatModel.tanTie | (intros; apply GlobalTheory.FlatModel.tanTie <;> assumption)
