import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisFrameMap
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
theorem _root_.GlobalTheory.T.tangent_basis_frame_map : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l' : Level H)
    (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype) (p : ℕ)
    [Fact p.Prime] (n : ℕ) [StarRing (𝓞 E)] (R : Type) [CommRing R] [IsDomain R] (ξ : Sp R ⟶ Y.X) (g : ℕ)
    (e : Fin g → (Sp (DualNumber R) ⟶ Y.t.G.left)), IsTanBasis Y.t ξ e →
    ∀ (P' : GlobalTheory.HTMap.FP Y.t ξ (p ^ n)) (κ : (Sp (FractionRing R) ⟶ Y.t.G.left) → Rˣ) (b : P'.Bˣ), P'.Gl κ b →
    ∀ x0 : R →+* 𝓞_ℂ_[p], P'.Full ((IsLocalRing.maximalIdeal 𝓞_ℂ_[p]).comap x0) →
    ∀ (yy : Sp ℂ_[p] ⟶ Xo'.XF c') (P : PtP E p) (π : P.G.left ⟶ Y.t.G.left) (ψ : P.A.A.left ⟶ Y.oF.t.G.left),
      PtOn Y (spMap x0 ≫ ξ) yy P π ψ → GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.LevelReduction P → ∀ tt : P.T,
      (∀ (β : P'.B →+* 𝓞_ℂ_[p]) (w : Sp 𝓞_ℂ_[p] ⟶ Y.t.G.left), P'.At x0 w β →
        ∀ z : GlobalTheory.ChTor.Pts P.A.A, z.left ≫ P.gen ≫ π = spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ w →
          algebraMap 𝓞_ℂ_[p] ℂ_[p] (β b) = (weil P.A (p ^ n) (tt.lev n) z : ℂ_[p])) →
    ∀ hvec : Fin g → 𝓞_ℂ_[p],
      (∀ (k : Fin g) (β : P'.B →+* DualNumber (𝓞_ℂ_[p] ⧸ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n})),
        P'.At ((algebraMap 𝓞_ℂ_[p] (DualNumber (𝓞_ℂ_[p] ⧸ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}))).comp x0)
          (spMap (dualMap (Ideal.Quotient.mk (Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}))) ≫ spMap (dualMap x0) ≫ e k) β →
        (β b).snd = Ideal.Quotient.mk (Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}) (hvec k)) →
    ∀ (k : Fin g) (x : LieG P.Gt), ITie P π x (spMap (dualMap x0) ≫ e k) →
      hvec k + (P.al₀ tt).1 x ∈ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n} := by
  first | exact @GlobalTheory.FinPartAt.levelHT_at_point | exact GlobalTheory.FinPartAt.levelHT_at_point | (intros; apply GlobalTheory.FinPartAt.levelHT_at_point <;> assumption)
