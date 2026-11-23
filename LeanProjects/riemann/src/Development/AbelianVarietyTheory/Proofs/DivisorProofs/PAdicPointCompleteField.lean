import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelPAdicComparisonStatement

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatModel

theorem pt_isEig_of_lieTie : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _))
    (p : ℕ) [Fact p.Prime] [StarRing (𝓞 E)] [Algebra c.F ℂ_[p]] (yb : Sp 𝓞_ℂ_[p] ⟶ Y.X) (yy : Sp ℂ_[p] ⟶ Xo'.XF c')
    (P : PtP E p) (π : P.G.left ⟶ Y.t.G.left) (ψ : P.A.A.left ⟶ Y.oF.t.G.left), PtOn Y yb yy P π ψ →
    ∀ (σ : E →+* ℂ) (x : LieG P.Gt) (u : Sp (DualNumber ℂ_[p]) ⟶ Xo.univ.t.G.left),
      LieTie P (ψ ≫ ν.φ) x u → IsEigAt c σ u → AvDefs.IsEig P.Gt P.oGt (embInt c P.integers σ) x := by
  intro E _ _ _ H Dw l l' Xo Xo' c c' W Y r ν p _ _ _ yb yy P π ψ hP σ x u h hu
  obtain ⟨-, -, h2, h3, h4, -⟩ := hP
  have hpb : IsGrpPullback P.A.A Xo.univ.t.G (yy ≫ r ≫ pullback.fst _ _) (ψ ≫ ν.φ) := h3.comp ν.cart
  have hact : ∀ a, (P.oA.act a).left ≫ (ψ ≫ ν.φ) = (ψ ≫ ν.φ) ≫ (Xo.univ.t.act.act a).left := fun a => by
    have e : (P.oA.act a).left ≫ ψ = ψ ≫ (Y.oF.t.act.act a).left := Y.m.cart.1.hom_ext
      (by rw [Category.assoc, Category.assoc, Y.m.act, h4, ← Category.assoc ψ, h4, ← Category.assoc, P.gen_act,
        Category.assoc, h2, Category.assoc])
      (by rw [Category.assoc, Category.assoc, Over.w, h3.1.w, Over.w_assoc])
    rw [← Category.assoc, e, Category.assoc, Category.assoc, ν.act]
  intro a
  exact (h.act a (hact a)).unique hpb.1 (by rw [hu a, ← algebraMap_embInt P.integers]; exact h.scale _)

end GlobalTheory.FlatModel

end
