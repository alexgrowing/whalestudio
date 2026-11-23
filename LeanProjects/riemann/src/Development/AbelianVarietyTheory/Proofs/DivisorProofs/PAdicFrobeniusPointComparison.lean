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

theorem lieTie_frameOf_of_ptAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F))
    (p : ℕ) [Fact p.Prime] [Algebra c.F ℂ_[p]] (P z : FrPt Xo c ℂ_[p]) (yb : Sp 𝓞_ℂ_[p] ⟶ Z.X),
    GlobalTheory.AllWt.ptF z = GlobalTheory.AllWt.ptF P →
    letI := H.starRing; ∀ (Q : PtP E p) (π : Q.G.left ⟶ Z.t.G.left) (ψ : Q.A.A.left ⟶ Z.oF.t.G.left),
      PtAt Z yb (GlobalTheory.AllWt.ptF P) Q π ψ → ∀ (σ : E →+* ℂ) (j : Fin (Dw.mult σ)) (xx : LieG Q.Gt),
      LieTie Q (ψ ≫ Z.m0.toSABMap.φ) xx (z.u σ j) → LieTie Q (Q.gen ≫ π) xx ((frameOf Z z).v σ j) := by
  intro E _ _ _ H Dw l Xo c Z p _ _ P z yb hz Q π ψ hP σ j xx h
  obtain ⟨xG, u', h1, h2, h3⟩ := h
  refine ⟨xG, u', h1, ?_, h3⟩
  obtain ⟨w, a1, a2, a3⟩ := (tie_frameOf Z z).2.2 σ j
  have hw := Over.w u'
  have hψ := hP.2.2.2.1.1.w
  have h5 := hP.2.2.2.2
  have hb : w ≫ Z.oF.t.G.hom = (Over.Hom.left u' ≫ ψ) ≫ Z.oF.t.G.hom := by
    rw [a1, Category.assoc, hψ, ← Category.assoc, hw, hz]
    rfl
  have hm : w ≫ Z.m0.φ = (Over.Hom.left u' ≫ ψ) ≫ Z.m0.φ := by
    rw [a2, Category.assoc, h2]
  have hwe := Z.m0.toSABMap.cart.1.hom_ext hm hb
  rw [← h5, ← Category.assoc, ← hwe, a3]

end GlobalTheory.DetHT
