import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelTangentOverInclusion
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecValAt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralPointPullbackComparison

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
theorem _root_.GlobalTheory.T.integral_model_tangent_over_inclusion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F), OverIncl r hle →
    ∀ (τ : Psi H) (A : Type) [CommRing A] (ξ : Sp A ⟶ Y.X) (β : c'.V W →+* A), ξ ≫ Y.s = spMap β →
    ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber A) ⟶ Y.t.G.left)) (U₁ h₁ : Fin (Dw.mult τ.1) → Fin g → A)
      (U₂ h₂ : Fin (Dw.mult (conjEmb τ.1)) → Fin g → A), IsTanBasis Y.t ξ e →
      (∀ (S : Type) [CommRing S] (φ : A →+* S),
        EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W τ.1))) (bcV Y.t φ e) (fun k b => φ (U₁ k b)) ∧
        EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W (conjEmb τ.1)))) (bcV Y.t φ e) fun k b => φ (U₂ k b)) →
      IsUnit (pairDet h₁ U₁) → IsUnit (pairDet h₂ U₂) →
    ∀ (L : Type) [CommRing L] [IsLocalRing L] (io : A →+* L) (yL : Sp L ⟶ Xo'.XF c'), yL ≫ Y.j = spMap io ≫ ξ →
    ∃ (_ : Algebra c.F L) (z : FrPt Xo c L) (w₁ : Fin (Dw.mult τ.1) → (Sp (DualNumber L) ⟶ Y.oF.t.G.left))
      (w₂ : Fin (Dw.mult (conjEmb τ.1)) → (Sp (DualNumber L) ⟶ Y.oF.t.G.left)),
      ptF z = yL ≫ r ∧
      (∀ i, IsCombAtG Y.t (yL ≫ Y.j) (bcV Y.t io e) (fun b => io (U₁ i b)) (w₁ i ≫ Y.m.φ)) ∧
      (∀ i, IsCombAtG Y.t (yL ≫ Y.j) (bcV Y.t io e) (fun b => io (U₂ i b)) (w₂ i ≫ Y.m.φ)) ∧
      (∀ i, z.u τ.1 i = w₁ i ≫ ν.φ) ∧ ∀ i, z.u (conjEmb τ.1) i = w₂ i ≫ ν.φ := by
  first | exact @GlobalTheory.FlatModel.FrameLoc.exists_frPt_of_chart | exact GlobalTheory.FlatModel.FrameLoc.exists_frPt_of_chart | (intros; apply GlobalTheory.FlatModel.FrameLoc.exists_frPt_of_chart <;> assumption)
