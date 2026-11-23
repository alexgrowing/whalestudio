import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducesPl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSectionFrameInvariance
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeExistsUniqueOfSamePoint
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsCombAtGMulVec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValueStatementHolds

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open scoped NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.FlatModel GlobalTheory.Toroidal
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.VertForm
open GlobalTheory.DetHT
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.ShFam.Descent

namespace GlobalTheory.DetHT

theorem ptAt_tangent_isEig : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F))
    (p : ℕ) [Fact p.Prime] [Algebra c.F ℂ_[p]] (z : FrPt Xo c ℂ_[p]) (yb : Sp 𝓞_ℂ_[p] ⟶ Z.X)
    (yy : Sp ℂ_[p] ⟶ Xo.XF c),
    letI := H.starRing; ∀ (Q : PtP E p) (π : Q.G.left ⟶ Z.t.G.left) (ψ : Q.A.A.left ⟶ Z.oF.t.G.left),
      PtAt Z yb yy Q π ψ → ∀ (σ : E →+* ℂ) (j : Fin (Dw.mult σ)) (xx : LieG Q.Gt),
      LieTie Q (ψ ≫ Z.m0.toSABMap.φ) xx (z.u σ j) → AvDefs.IsEig Q.Gt Q.oGt (embInt c Q.integers σ) xx := by
  intro E _ _ _ H Dw l Xo c Z p _ _ z yb yy
  letI := H.starRing
  intro Q π ψ hP σ j xx h
  obtain ⟨-, -, h3, h4, h5⟩ := hP
  have hpb : IsGrpPullback Q.A.A Xo.univ.t.G _ (ψ ≫ Z.m0.toSABMap.φ) := h4.comp Z.m0.toSABMap.cart
  have hact : ∀ a, (Q.oA.act a).left ≫ (ψ ≫ Z.m0.toSABMap.φ) =
      (ψ ≫ Z.m0.toSABMap.φ) ≫ (Xo.univ.t.act.act a).left := fun a => by
    have e : (Q.oA.act a).left ≫ ψ = ψ ≫ (Z.oF.t.act.act a).left := Z.m.cart.1.hom_ext
      (by rw [Category.assoc, Category.assoc, Z.m.act, h5, ← Category.assoc ψ, h5, ← Category.assoc, Q.gen_act,
        Category.assoc, h3, Category.assoc])
      (by rw [Category.assoc, Category.assoc, Over.w, h4.1.w, Over.w_assoc])
    rw [← Category.assoc, e, Category.assoc, Category.assoc, Z.m0.toSABMap.act]
  exact fun a =>
    (h.act a (hact a)).unique hpb.1 (by rw [z.eig σ j a, ← algebraMap_embInt Q.integers]; exact h.scale _)

end GlobalTheory.DetHT
